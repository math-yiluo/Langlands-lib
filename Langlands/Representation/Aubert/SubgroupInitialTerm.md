# Canonical identification of the initial actual subgroup term

This internal construction identifies a smooth representation `ρ` with the
actual subgroup induction–coinvariant term for `P = G`, `U = {1}`.
All declarations lie in `Langlands.Aubert.SubgroupTransition`.
Author: Worker 194.

`top_normalizes_bot` verifies the required subgroup normalization.
`relations_bot` proves that trivial-character localization at the trivial
subgroup has zero relation submodule: each generating relation is
`ρ(1)v - v = 0`. No representation-theoretic hypothesis is used.

The existing canonical orbit-function map `augmentation` is injective in
this case (`initial_augmentation_injective`): evaluate at the identity and
use the exact quotient relation criterion and `relations_bot`. It is
surjective (`initial_augmentation_surjective`): choose a representative
of the function's value at the identity, then use covariance under the
full subgroup to recover every value of the function.

`initialEquiv` packages this bijective actual intertwiner as an equivalence
of representations. `initialEquiv_eval` records its formula
`v ↦ (g ↦ [ρ(g)v])`. The input smoothness premise is exactly the premise
used by `augmentation` to obtain smooth orbit functions. There is no
finite-length, admissibility, rank or field-characteristic premise.

This equivalence supplies the initial-term identification for a subgroup
family whose empty removed-root set has `P = G` and `U = {1}`. Establishing
those identities for the shared actual standard-parabolic framework and
the normalized induction/Jacquet comparison remains separate. In
particular this unit makes no corrected exactness or terminal-vanishing
claim. Its provenance is the existing quotient relations, covariance and
canonical augmentation, whose intrinsic laws are proved here.
