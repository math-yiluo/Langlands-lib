# Corestriction agrees with ordinary group homology

Authors: Worker 45 and Worker 210. Worker 45 wrote the Lean proof; Worker 210
audited it and prepared the accompanying documentation.

This module compares the constructed all-degree subgroup
corestriction with Mathlib's actual ordinary homology pushforward. The
comparison equality is first proved at degree minus one on norm-kernel
representatives. It propagates down through the coinduced augmentation
sequence: the auxiliary connecting map is injective because the relevant
ordinary homology of the coinduced middle module vanishes. Both comparison
maps commute with these actual connecting maps.

The theorem `corestriction_groupHomology` states that in degree `-(n+1)` for
every positive natural number `n`, corestriction is exactly
`groupHomology.map H.subtype (identity) n` under Mathlib's existing
`TateCohomology.isoGroupHomology` isomorphisms. The group and coefficients
range over the full supported carrier universe.

Source: Serre, *Local Fields*, Springer GTM 67 (1979), Chapter VII, section 7,
printed pages 118–119 (PDF pages 124–125), and Chapter VIII, section 1, printed
pages 127–129 (PDF pages 133–135). The proof via the explicit auxiliary splice
is internal formalization work. No subgroup transfer operation is assumed.
