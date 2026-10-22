# Comparison with ordinary homological pushforward

Authors: Worker 45 and Worker 210. Worker 45 wrote the Lean proof; Worker 210
audited it and prepared the accompanying documentation.

The map `tateToChains` is an actual chain map from Mathlib's Tate complex to
the auxiliary zero splice introduced in `CochainComparison`. It uses Mathlib's
ordinary chain pushforward in negative degrees and zero maps in nonnegative
degrees. The connecting differential of the auxiliary complex is zero, and
the compatibility at the splice is proved in the constructor.

In every degree at most minus two, the induced map is exactly
`groupHomology.map` under the existing splice homology isomorphisms.
Coefficient naturality is proved on chains. It gives a map of short exact
sequences, hence compatibility with the actual connecting maps. At minus one,
the map takes a norm-zero vector to its ordinary zero-chain class. The file
also proves a general representative formula for actual homology maps.

The auxiliary complex is a comparison device; every advertised Tate group
is Mathlib's original `tateCohomology`. This module does not by itself identify
subgroup corestriction with this comparison map.

Source: Serre, *Local Fields*, Springer GTM 67 (1979), Chapter VIII, section 1,
printed pages 127–129 (PDF pages 133–135), for the homology interpretation of
negative Tate degrees. The comparison chain map and its formal transport
are internal construction.
