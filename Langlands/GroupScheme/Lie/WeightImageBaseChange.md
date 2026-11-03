# Opposite-weight Lie-image witnesses under field extension

Author: Worker 1462.

`Lie.MeetsOppositeWeightSpaces j i α` abbreviates the conjunction of
`Lie.MeetsWeightSpace j i α` and `Lie.MeetsWeightSpace j i (-α)`. Thus each
of the two opposite character weight spaces contains a nonzero vector
with an actual dual-number identity-kernel preimage under `i`. The
vectors for the two weights may differ. This definition works over any
commutative base ring, with affine ambient group scheme `G`, commutative
acting group scheme `T`, and arbitrary group scheme `H` mapping to `G`.
It imposes no root or nonzero-character condition.

The transport lemmas assume fields `k` and `K` in the original universe
`u`, an algebra structure `k → K`, and that `G` is affine and locally of
finite type over `k`. Write `b = algebraBaseMap k K`. The group schemes
over `K` and their homomorphisms are the actual scheme pullbacks.

`Lie.MeetsWeightSpace.baseChange` reuses
`weightSpace_lieImage_baseChange` from `Lie.FieldExtension`. That result
extends a supplied nonzero ambient vector using the canonical
scalar-extension equivalence, extends its actual kernel preimage by
`Lie.kernelFieldExtension`, and proves the required image equation by
naturality. Injectivity of field extension on the ambient Lie kernel
preserves nonzeroness. The weight condition is the existing adjoint
condition after every commutative test algebra.

`Lie.MeetsOppositeWeightSpaces.baseChange` applies that result to both
witnesses. Additivity of actual character pullback identifies the image
of `-α` with the negative of the image of `α`. The two transported
witnesses therefore lie in exactly the opposite weight spaces for the
same pulled-back subgroup homomorphism.

`Lie.not_meetsOppositeWeightSpaces_of_baseChange` is the contrapositive:
an exclusion for the pulled-back character and subgroup implies the
original exclusion. No splitness, maximality, reductivity, smoothness,
connectedness, closedness or solvability is required for these
characterwise transport and descent results; no additional hypothesis
is imposed on `H` or `i`.

`Lie.not_meetsOppositeWeightSpaces_on_roots_of_baseChange` additionally
assumes that `T` is split. For an original root `α`, the published
`mem_roots_baseChange_iff` from `Torus.RootSupportBaseChange` supplies
membership of its actual pulled-back character in the target root set.
The assumed exclusion at that root then descends by the characterwise
lemma. No root-negation theorem is required, since the opposite weight
space is defined for every character.

This is internal derived infrastructure combining `Lie.WeightImage`,
`Lie.FieldExtension` and `Torus.RootSupportBaseChange`; it introduces no
external structural assertion. It retains arbitrary characteristic and
imperfect fields. The final lemma assumes exclusion after extension;
it proves neither that exclusion nor the geometric properties of
pulled-back tori or subgroups needed to obtain it. In particular it does
not prove `RankOneSolvableObstructionStatement` or any rank-one Borel
classification.
