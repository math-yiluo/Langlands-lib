# Reflection compatibility of root-datum isogenies

This internal derived module proves that a supplied isogeny of finite reduced
root data intertwines the permutations of roots induced by corresponding
reflections. The root factors are constant along those reflections. In
particular, the factors at a root and its opposite are equal.

The existing `weightMap_reflection` identity and the root image formula give
an equality of two positive integral multiples of target roots. These roots
are linearly dependent, so reducedness makes them equal or opposite.
Pairing with the target coroot rules out the opposite case because both
multipliers are positive. The same pairing then identifies the multipliers;
injectivity of the target root indexing identifies the roots.

The proposition `PreservesReflections` packages the factor and index identities,
and `preservesReflections` proves it for every supplied isogeny.
`reflectionPerm_compatibility` gives the two identities at individual roots.
`rootFactor_reflectionPerm` and `indexEquiv_reflectionPerm` project them, and
`indexEquiv_symm_reflectionPerm` supplies the inverse-index formula. The result
uses the actual lattice maps of `RootDatumIsogeny`; no choice of bases,
centrality assumption, or equality of factors at unrelated roots is required.
