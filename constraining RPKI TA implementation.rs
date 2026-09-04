// Interval indexes and trust-anchor resource constraint evaluation.


use std::collections::{BTreeMap, BTreeSet};
use std::net::{IpAddr, Ipv4Addr, Ipv6Addr};
use std::ops::Deref;
use std::path::{Path, PathBuf};

use sha2::Digest;

use crate::data_model::rc::{
    Afi, AsIdOrRange, AsIdentifierChoice, IpAddressChoice, IpAddressOrRange, IpResourceSet,
    ResourceCertificate,
};
use crate::parallel::types::{TalInputSpec, TalSource};

const LINEAR_INTERVAL_THRESHOLD: usize = 10;

/// A normalized rule set with a small-set linear path and a large-set tree path.
///
/// The parser constructs this only after sorting and merging overlapping or
/// adjacent intervals. The tree lookup therefore only needs to inspect the
/// predecessor of a target interval; normalized intervals are disjoint and
/// sorted by their lower bound.
#[derive(Clone)]
struct IntervalIndex<I> {
    rules: Vec<I>,
    lookup: IntervalLookup,
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum IntervalLookup {
    Linear,
    Tree(BTreeMap<u128, u128>),
}

impl<I: std::fmt::Debug> std::fmt::Debug for IntervalIndex<I> {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // Keep derived acceleration data out of Debug so diagnostics continue
        // to describe canonical rules rather than their index layout.
        self.rules.fmt(formatter)
    }
}

impl<I: PartialEq> PartialEq for IntervalIndex<I> {
    fn eq(&self, other: &Self) -> bool {
        self.rules == other.rules
    }
}

impl<I: Eq> Eq for IntervalIndex<I> {}

impl<I> Deref for IntervalIndex<I> {
    type Target = [I];

    fn deref(&self) -> &Self::Target {
        &self.rules
    }
}

trait IntervalValue {
    fn start(&self) -> u128;
    fn end(&self) -> u128;
    fn overlaps(&self, other: &Self) -> bool;
}

impl<I: IntervalValue> IntervalIndex<I> {
    fn new(rules: Vec<I>) -> Self {
        debug_assert!(
            rules
                .windows(2)
                .all(|window| { window[0].end().saturating_add(1) < window[1].start() })
        );
        let lookup = if rules.len() > LINEAR_INTERVAL_THRESHOLD {
            let tree = rules
                .iter()
                .map(|rule| (rule.start(), rule.end()))
                .collect();
            IntervalLookup::Tree(tree)
        } else {
            IntervalLookup::Linear
        };
        Self { rules, lookup }
    }

    fn any_overlaps(&self, target: &I) -> bool {
        match &self.lookup {
            IntervalLookup::Linear => self.rules.iter().any(|entry| entry.overlaps(target)),
            IntervalLookup::Tree(tree) => tree
                .range(..=target.end())
                .next_back()
                .map(|(_, end)| *end >= target.start())
                .unwrap_or(false),
        }
    }

    fn fully_covers(&self, target: &I) -> bool {
        match &self.lookup {
            IntervalLookup::Linear => self.fully_covers_linear(target),
            IntervalLookup::Tree(tree) => tree
                .range(..=target.start())
                .next_back()
                .map(|(_, end)| *end >= target.end())
                .unwrap_or(false),
        }
    }

    fn fully_covers_linear(&self, target: &I) -> bool {
        let mut cursor = target.start();
        for entry in &self.rules {
            if entry.end() < cursor {
                continue;
            }
            if entry.start() > cursor {
                return false;
            }
            if entry.end() >= target.end() {
                return true;
            }
            cursor = entry.end().saturating_add(1);
        }
        false
    }

    #[cfg(test)]
    fn uses_tree(&self) -> bool {
        matches!(self.lookup, IntervalLookup::Tree(_))
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TaConstraintsByTal {
    by_tal_id: BTreeMap<String, std::sync::Arc<TaConstraints>>,
    /// Stable semantic digest of the normalized rules.  This is computed once
    /// while loading the run policy so cache identity checks do not serialize
    /// every rule for every publication point.
    fingerprint: [u8; 32],
}

impl TaConstraintsByTal {
    pub fn load_for_tals(
        tal_inputs: &[TalInputSpec],
        explicit_specs: &[String],
    ) -> Result<Self, String> {
        let tal_ids = tal_inputs
            .iter()
            .map(|input| input.tal_id.as_str())
            .collect::<BTreeSet<_>>();
        let mut explicit_paths = BTreeMap::<String, PathBuf>::new();
        for spec in explicit_specs {
            let (tal_id, path) = spec
                .split_once('=')
                .ok_or_else(|| format!("--ta-constraints expects <tal-id>=<path>, got '{spec}'"))?;
            let tal_id = tal_id.trim();
            let path = path.trim();
            if tal_id.is_empty() || path.is_empty() {
                return Err(format!(
                    "--ta-constraints expects non-empty <tal-id>=<path>, got '{spec}'"
                ));
            }
            if !tal_ids.contains(tal_id) {
                return Err(format!(
                    "--ta-constraints references unknown TAL id '{tal_id}'"
                ));
            }
            if explicit_paths
                .insert(tal_id.to_string(), PathBuf::from(path))
                .is_some()
            {
                return Err(format!(
                    "--ta-constraints specifies TAL id '{tal_id}' more than once"
                ));
            }
        }

        let mut by_tal_id = BTreeMap::new();
        for input in tal_inputs {
            let path = explicit_paths
                .get(&input.tal_id)
                .cloned()
                .or_else(|| adjacent_constraints_path(&input.source).filter(|path| path.is_file()));
            if let Some(path) = path {
                let constraints = TaConstraints::from_file(&path).map_err(|error| {
                    format!(
                        "load TA constraints for '{}' from {} failed: {error}",
                        input.tal_id,
                        path.display()
                    )
                })?;
                by_tal_id.insert(input.tal_id.clone(), std::sync::Arc::new(constraints));
            }
        }
        let fingerprint = constraints_fingerprint(&by_tal_id);
        Ok(Self {
            by_tal_id,
            fingerprint,
        })
    }

    pub fn for_tal(&self, tal_id: &str) -> Option<&TaConstraints> {
        self.by_tal_id.get(tal_id).map(std::sync::Arc::as_ref)
    }

    /// Return the immutable, process-local snapshot for a TAL without cloning
    /// the rule trees.  Phase-2 object workers own this `Arc` in their task
    /// payload, while scoped stage workers borrow the same policy map.
    pub(crate) fn shared_for_tal(&self, tal_id: &str) -> Option<std::sync::Arc<TaConstraints>> {
        self.by_tal_id.get(tal_id).cloned()
    }

    pub fn is_empty(&self) -> bool {
        self.by_tal_id.is_empty()
    }

    pub fn configuration_warnings(&self) -> Vec<String> {
        self.by_tal_id
            .iter()
            .flat_map(|(tal_id, constraints)| {
                constraints.warnings().iter().map(move |warning| {
                    format!(
                        "TA constraints for TAL '{tal_id}' ({}): {warning}",
                        constraints.source().display()
                    )
                })
            })
            .collect()
    }

    /// Return the precomputed SHA-256 digest of the normalized semantic rules.
    ///
    /// The returned bytes are stable across source paths and derived index
    /// layouts, and are intentionally borrowed so hot-path cache lookups do
    /// not allocate.
    pub fn fingerprint_bytes(&self) -> &[u8] {
        &self.fingerprint
    }

    pub fn fingerprint_sha256_hex(&self) -> String {
        hex::encode(self.fingerprint)
    }
}

impl Default for TaConstraintsByTal {
    fn default() -> Self {
        let by_tal_id = BTreeMap::new();
        let fingerprint = constraints_fingerprint(&by_tal_id);
        Self {
            by_tal_id,
            fingerprint,
        }
    }
}

const CONSTRAINTS_FINGERPRINT_VERSION: &[u8] = b"ta-constraints-semantic-v1";

fn constraints_fingerprint(
    by_tal_id: &BTreeMap<String, std::sync::Arc<TaConstraints>>,
) -> [u8; 32] {
    let mut hasher = sha2::Sha256::new();
    hasher.update(CONSTRAINTS_FINGERPRINT_VERSION);
    hasher.update((by_tal_id.len() as u64).to_be_bytes());
    for (tal_id, constraints) in by_tal_id {
        update_length_prefixed(&mut hasher, tal_id.as_bytes());
        update_ip_intervals(&mut hasher, b"allow-v4", &constraints.allow_v4);
        update_ip_intervals(&mut hasher, b"deny-v4", &constraints.deny_v4);
        update_ip_intervals(&mut hasher, b"allow-v6", &constraints.allow_v6);
        update_ip_intervals(&mut hasher, b"deny-v6", &constraints.deny_v6);
        update_as_intervals(&mut hasher, b"allow-asn", &constraints.allow_asn);
        update_as_intervals(&mut hasher, b"deny-asn", &constraints.deny_asn);
    }
    let digest = hasher.finalize();
    let mut out = [0u8; 32];
    out.copy_from_slice(&digest);
    out
}

fn update_length_prefixed(hasher: &mut sha2::Sha256, value: &[u8]) {
    hasher.update((value.len() as u64).to_be_bytes());
    hasher.update(value);
}

fn update_ip_intervals(
    hasher: &mut sha2::Sha256,
    label: &[u8],
    intervals: &IntervalIndex<IpInterval>,
) {
    update_length_prefixed(hasher, label);
    hasher.update((intervals.rules.len() as u64).to_be_bytes());
    for interval in &intervals.rules {
        hasher.update([match interval.afi {
            Afi::Ipv4 => 4,
            Afi::Ipv6 => 6,
        }]);
        hasher.update(interval.min.to_be_bytes());
        hasher.update(interval.max.to_be_bytes());
    }
}

fn update_as_intervals(
    hasher: &mut sha2::Sha256,
    label: &[u8],
    intervals: &IntervalIndex<AsInterval>,
) {
    update_length_prefixed(hasher, label);
    hasher.update((intervals.rules.len() as u64).to_be_bytes());
    for interval in &intervals.rules {
        hasher.update(interval.min.to_be_bytes());
        hasher.update(interval.max.to_be_bytes());
    }
}

fn adjacent_constraints_path(source: &TalSource) -> Option<PathBuf> {
    match source {
        TalSource::FilePath(path) => Some(path.with_extension("constraints")),
        TalSource::FilePathWithTa { tal_path, .. } => Some(tal_path.with_extension("constraints")),
        TalSource::Url(_) | TalSource::DerBytes { .. } => None,
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TaConstraints {
    source: PathBuf,
    allow_v4: IntervalIndex<IpInterval>,
    deny_v4: IntervalIndex<IpInterval>,
    allow_v6: IntervalIndex<IpInterval>,
    deny_v6: IntervalIndex<IpInterval>,
    allow_asn: IntervalIndex<AsInterval>,
    deny_asn: IntervalIndex<AsInterval>,
    warnings: Vec<String>,
}

impl TaConstraints {
    pub fn from_file(path: &Path) -> Result<Self, String> {
        let contents = std::fs::read_to_string(path)
            .map_err(|error| format!("read {}: {error}", path.display()))?;
        Self::parse(path.to_path_buf(), &contents)
    }

    pub fn warnings(&self) -> &[String] {
        &self.warnings
    }

    pub fn source(&self) -> &Path {
        &self.source
    }

    pub fn validate_ee_certificate(
        &self,
        certificate: &ResourceCertificate,
    ) -> Result<(), TaConstraintsViolation> {
        if let Some(ip_resources) = certificate.tbs.extensions.ip_resources.as_ref() {
            self.validate_ip_resources(ip_resources)?;
        }
        if let Some(as_resources) = certificate.tbs.extensions.as_resources.as_ref() {
            self.validate_as_choice("AS", as_resources.asnum.as_ref())?;
            self.validate_as_choice("RDI", as_resources.rdi.as_ref())?;
        }
        Ok(())
    }

    fn parse(source: PathBuf, contents: &str) -> Result<Self, String> {
        let mut allow_v4 = Vec::new();
        let mut deny_v4 = Vec::new();
        let mut allow_v6 = Vec::new();
        let mut deny_v6 = Vec::new();
        let mut allow_asn = Vec::new();
        let mut deny_asn = Vec::new();

        for (index, raw_line) in contents.lines().enumerate() {
            let line_number = index + 1;
            let line = raw_line.split('#').next().unwrap_or("").trim();
            if line.is_empty() {
                continue;
            }
            let mut words = line.split_whitespace();
            let action = words.next().expect("non-empty line has first word");
            let resource = words.collect::<Vec<_>>().join(" ");
            if resource.is_empty() {
                return Err(format!(
                    "line {line_number}: missing resource after '{action}'"
                ));
            }
            let allow = match action {
                "allow" => true,
                "deny" => false,
                _ => {
                    return Err(format!(
                        "line {line_number}: expected 'allow' or 'deny', got '{action}'"
                    ));
                }
            };
            if looks_like_ip_resource(&resource) {
                let interval = parse_ip_interval(&resource).map_err(|error| {
                    format!("line {line_number}: invalid IP resource '{resource}': {error}")
                })?;
                match (interval.afi, allow) {
                    (Afi::Ipv4, true) => allow_v4.push(interval),
                    (Afi::Ipv4, false) => deny_v4.push(interval),
                    (Afi::Ipv6, true) => allow_v6.push(interval),
                    (Afi::Ipv6, false) => deny_v6.push(interval),
                }
            } else {
                let interval = parse_as_interval(&resource).map_err(|error| {
                    format!("line {line_number}: invalid AS resource '{resource}': {error}")
                })?;
                if allow {
                    allow_asn.push(interval);
                } else {
                    deny_asn.push(interval);
                }
            }
        }

        let mut warnings = Vec::new();
        normalize_ip_intervals("allow IPv4", &mut allow_v4, &mut warnings);
        normalize_ip_intervals("deny IPv4", &mut deny_v4, &mut warnings);
        normalize_ip_intervals("allow IPv6", &mut allow_v6, &mut warnings);
        normalize_ip_intervals("deny IPv6", &mut deny_v6, &mut warnings);
        normalize_as_intervals("allow AS", &mut allow_asn, &mut warnings);
        normalize_as_intervals("deny AS", &mut deny_asn, &mut warnings);

        Ok(Self {
            source,
            allow_v4: IntervalIndex::new(allow_v4),
            deny_v4: IntervalIndex::new(deny_v4),
            allow_v6: IntervalIndex::new(allow_v6),
            deny_v6: IntervalIndex::new(deny_v6),
            allow_asn: IntervalIndex::new(allow_asn),
            deny_asn: IntervalIndex::new(deny_asn),
            warnings,
        })
    }

    fn validate_ip_resources(
        &self,
        resources: &IpResourceSet,
    ) -> Result<(), TaConstraintsViolation> {
        for family in &resources.families {
            let items = match &family.choice {
                // Constraints apply to explicit INR listings.  EE profiles for
                // constrained signed objects already reject inappropriate inherit.
                IpAddressChoice::Inherit => continue,
                IpAddressChoice::AddressesOrRanges(items) => items,
            };
            let (allow, deny) = match family.afi {
                Afi::Ipv4 => (&self.allow_v4, &self.deny_v4),
                Afi::Ipv6 => (&self.allow_v6, &self.deny_v6),
            };
            for item in items {
                let interval = ip_item_to_interval(family.afi, item)?;
                if deny.any_overlaps(&interval) {
                    return Err(TaConstraintsViolation(format!(
                        "{} {} intersects a deny rule in {}",
                        afi_name(family.afi),
                        interval,
                        self.source.display()
                    )));
                }
                if !allow.fully_covers(&interval) {
                    return Err(TaConstraintsViolation(format!(
                        "{} {} is not fully contained in allow rules in {}",
                        afi_name(family.afi),
                        interval,
                        self.source.display()
                    )));
                }
            }
        }
        Ok(())
    }

    fn validate_as_choice(
        &self,
        kind: &str,
        choice: Option<&AsIdentifierChoice>,
    ) -> Result<(), TaConstraintsViolation> {
        let Some(choice) = choice else {
            return Ok(());
        };
        let items = match choice {
            AsIdentifierChoice::Inherit => return Ok(()),
            AsIdentifierChoice::AsIdsOrRanges(items) => items,
        };
        for item in items {
            let interval = match item {
                AsIdOrRange::Id(value) => AsInterval::new(*value, *value),
                AsIdOrRange::Range { min, max } => AsInterval::new(*min, *max),
            };
            if self.deny_asn.any_overlaps(&interval) {
                return Err(TaConstraintsViolation(format!(
                    "{kind} {interval} intersects a deny rule in {}",
                    self.source.display()
                )));
            }
            if !self.allow_asn.fully_covers(&interval) {
                return Err(TaConstraintsViolation(format!(
                    "{kind} {interval} is not fully contained in allow rules in {}",
                    self.source.display()
                )));
            }
        }
        Ok(())
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TaConstraintsViolation(pub String);

impl std::fmt::Display for TaConstraintsViolation {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(formatter)
    }
}

impl std::error::Error for TaConstraintsViolation {}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct IpInterval {
    afi: Afi,
    min: u128,
    max: u128,
}

impl IpInterval {
    fn new(afi: Afi, min: u128, max: u128) -> Self {
        Self { afi, min, max }
    }

    fn overlaps(&self, other: &Self) -> bool {
        self.afi == other.afi && self.min <= other.max && other.min <= self.max
    }
}

impl IntervalValue for IpInterval {
    fn start(&self) -> u128 {
        self.min
    }

    fn end(&self) -> u128 {
        self.max
    }

    fn overlaps(&self, other: &Self) -> bool {
        IpInterval::overlaps(self, other)
    }
}

impl std::fmt::Display for IpInterval {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let min = u128_to_ip(self.afi, self.min);
        let max = u128_to_ip(self.afi, self.max);
        if min == max {
            write!(formatter, "{min}")
        } else {
            write!(formatter, "{min} - {max}")
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct AsInterval {
    min: u32,
    max: u32,
}

impl AsInterval {
    fn new(min: u32, max: u32) -> Self {
        Self { min, max }
    }

    fn overlaps(&self, other: &Self) -> bool {
        self.min <= other.max && other.min <= self.max
    }
}

impl IntervalValue for AsInterval {
    fn start(&self) -> u128 {
        self.min.into()
    }

    fn end(&self) -> u128 {
        self.max.into()
    }

    fn overlaps(&self, other: &Self) -> bool {
        AsInterval::overlaps(self, other)
    }
}

impl std::fmt::Display for AsInterval {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.min == self.max {
            write!(formatter, "{}", self.min)
        } else {
            write!(formatter, "{} - {}", self.min, self.max)
        }
    }
}

fn looks_like_ip_resource(resource: &str) -> bool {
    resource.contains('.') || resource.contains(':') || resource.contains('/')
}

fn parse_ip_interval(resource: &str) -> Result<IpInterval, String> {
    if let Some((raw_min, raw_max)) = resource.split_once('-') {
        let min: IpAddr = raw_min.trim().parse().map_err(|_| "invalid range start")?;
        let max: IpAddr = raw_max.trim().parse().map_err(|_| "invalid range end")?;
        let (afi, min) = ip_to_u128(min);
        let (max_afi, max) = ip_to_u128(max);
        if afi != max_afi {
            return Err("range endpoints use different address families".to_string());
        }
        if min > max {
            return Err("range start is greater than range end".to_string());
        }
        return Ok(IpInterval::new(afi, min, max));
    }

    let (raw_address, raw_prefix_len) = resource
        .split_once('/')
        .ok_or_else(|| "expected CIDR prefix or range".to_string())?;
    let address: IpAddr = raw_address.trim().parse().map_err(|_| "invalid address")?;
    let prefix_len: u16 = raw_prefix_len
        .trim()
        .parse()
        .map_err(|_| "invalid prefix length")?;
    let (afi, address) = ip_to_u128(address);
    let width = match afi {
        Afi::Ipv4 => 32,
        Afi::Ipv6 => 128,
    };
    if prefix_len > width {
        return Err(format!("prefix length must be <= {width}"));
    }
    let host_bits = width - prefix_len;
    let mask = if prefix_len == 0 {
        0
    } else {
        width_mask(width) << host_bits
    };
    let min = address & mask;
    let max = min | (!mask & width_mask(width));
    Ok(IpInterval::new(afi, min, max))
}

fn parse_as_interval(resource: &str) -> Result<AsInterval, String> {
    let parse_asn = |raw: &str| -> Result<u32, String> {
        raw.trim()
            .strip_prefix("AS")
            .or_else(|| raw.trim().strip_prefix("as"))
            .unwrap_or(raw.trim())
            .parse::<u32>()
            .map_err(|_| "expected an ASN in the range 0..4294967295".to_string())
    };
    if let Some((raw_min, raw_max)) = resource.split_once('-') {
        let min = parse_asn(raw_min)?;
        let max = parse_asn(raw_max)?;
        if min > max {
            return Err("range start is greater than range end".to_string());
        }
        Ok(AsInterval::new(min, max))
    } else {
        let value = parse_asn(resource)?;
        Ok(AsInterval::new(value, value))
    }
}

fn normalize_ip_intervals(label: &str, entries: &mut Vec<IpInterval>, warnings: &mut Vec<String>) {
    entries.sort_by_key(|entry| (entry.min, entry.max));
    let mut normalized = Vec::with_capacity(entries.len());
    for entry in entries.drain(..) {
        let Some(last) = normalized.last_mut() else {
            normalized.push(entry);
            continue;
        };
        if entry.min <= last.max {
            warnings.push(format!(
                "TA constraints {label} rules overlap; normalized without blocking startup"
            ));
            last.max = last.max.max(entry.max);
        } else if entry.min == last.max.saturating_add(1) {
            last.max = entry.max;
        } else {
            normalized.push(entry);
        }
    }
    warnings.sort();
    warnings.dedup();
    *entries = normalized;
}

fn normalize_as_intervals(label: &str, entries: &mut Vec<AsInterval>, warnings: &mut Vec<String>) {
    entries.sort_by_key(|entry| (entry.min, entry.max));
    let mut normalized = Vec::with_capacity(entries.len());
    for entry in entries.drain(..) {
        let Some(last) = normalized.last_mut() else {
            normalized.push(entry);
            continue;
        };
        if entry.min <= last.max {
            warnings.push(format!(
                "TA constraints {label} rules overlap; normalized without blocking startup"
            ));
            last.max = last.max.max(entry.max);
        } else if entry.min == last.max.saturating_add(1) {
            last.max = entry.max;
        } else {
            normalized.push(entry);
        }
    }
    warnings.sort();
    warnings.dedup();
    *entries = normalized;
}

fn ip_item_to_interval(
    afi: Afi,
    item: &IpAddressOrRange,
) -> Result<IpInterval, TaConstraintsViolation> {
    let (min, max) = match item {
        IpAddressOrRange::Prefix(prefix) => {
            let width = prefix.afi.ub();
            let address = ip_bytes_to_u128(&prefix.addr);
            let prefix_len = prefix.prefix_len.min(width);
            let host_bits = width - prefix_len;
            let mask = if prefix_len == 0 {
                0
            } else {
                width_mask(width) << host_bits
            };
            let min = address & mask;
            (min, min | (!mask & width_mask(width)))
        }
        IpAddressOrRange::Range(range) => {
            (ip_bytes_to_u128(&range.min), ip_bytes_to_u128(&range.max))
        }
    };
    if min > max {
        return Err(TaConstraintsViolation(
            "EE certificate carries an invalid IP range".to_string(),
        ));
    }
    Ok(IpInterval::new(afi, min, max))
}

fn ip_to_u128(address: IpAddr) -> (Afi, u128) {
    match address {
        IpAddr::V4(address) => (Afi::Ipv4, u32::from(address) as u128),
        IpAddr::V6(address) => (Afi::Ipv6, u128::from(address)),
    }
}

fn ip_bytes_to_u128(bytes: &[u8]) -> u128 {
    bytes
        .iter()
        .fold(0u128, |value, byte| (value << 8) | u128::from(*byte))
}

fn width_mask(width: u16) -> u128 {
    if width == 128 {
        u128::MAX
    } else {
        (1u128 << width) - 1
    }
}

fn u128_to_ip(afi: Afi, value: u128) -> IpAddr {
    match afi {
        Afi::Ipv4 => IpAddr::V4(Ipv4Addr::from(value as u32)),
        Afi::Ipv6 => IpAddr::V6(Ipv6Addr::from(value)),
    }
}

fn afi_name(afi: Afi) -> &'static str {
    match afi {
        Afi::Ipv4 => "IPv4",
        Afi::Ipv6 => "IPv6",
    }
}
