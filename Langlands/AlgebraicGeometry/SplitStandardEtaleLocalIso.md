# Split standard etale algebras

This internal construction supplies actual open sections of standard etale
algebras whose monic presentation polynomial splits over the base domain. It
proves that the associated spectrum map is a Zariski local isomorphism. The base
domain is arbitrary; no valuation hypothesis is needed for this construction.

`monic_splits_of_isAlgClosed_fractionField` proves that every monic polynomial
over an integrally closed domain with algebraically closed fraction field splits
already over the domain: each fraction-field root is integral and hence belongs
to the domain, and splitting reflects along the injective coefficient map.

For an actual standard etale presentation, `exists_baseRoot_of_splits` shows
that the presentation generator at any field-valued point equals a root in the
base. It evaluates the split product into that field, selects a zero factor,
and retains both the actual root equation and the coordinate equality.
`rootSection` then constructs an actual algebra map to the localization at the
root's g-value, with its generator equation. These are internal consequences of
Mathlib's split polynomial, integral closure and standard etale interfaces.

`exists_rootSection_factor` constructs a map from the localization to any given
field-valued point and verifies that its composite with the root section equals
the original point as an algebra homomorphism. It uses the presentation's
homomorphism extensionality on its distinguished generator.

`rootSectionMap` is the actual spectrum map of that section. Its composite with
the standard etale structure morphism is exactly the principal base-open map.
The section map is etale by cancellation of the etale structure map and is a
monomorphism since its composite is an open immersion. A flat locally finitely
presented monomorphism is an open immersion, so each root section is open.

`SplitStandardEtale.isLocalIso_of_splits` applies the field-point factorization
to the actual residue-field map at every source point. The exact factorization
shows the point belongs to one root section's open image, and that section's
composite with the original map is a principal base open. Hence the original
map is source-locally an open immersion, which is the existing `IsLocalIso`
predicate. This proves the promised local isomorphism for a supplied split
standard etale presentation.

The provenance is internal composition of Mathlib's integral-closure, polynomial
splitting, actual standard etale presentations, residue-field maps and flat
monomorphism interfaces. This module does not assert that all etale maps over
arbitrary bases are local isomorphisms, or prove valuation affineness itself.
