# Nonmultipliable opposite-factor consequences from absent higher roots

Over an arbitrary field and universe, this internal module proves the
equal-factor, conjugation and actual torus-square conclusions for a
supplied normalizing opposite pair, assuming that all second and later
positive multiples of each of the two opposite characters are absent
from the actual relative-root set. The group is affine and smooth, the
torus is split, and its map into the group is monomorphic on underlying
schemes. These hypotheses are explicit; connected reductivity and maximal
splitness are not needed for the results in this module.

The provenance is an internal deduction from the published actual cyclic
comparison and filtration proofs,
[`CyclicRootFunctorComparisonProof`](CyclicRootFunctorComparisonProof.md)
and [`CyclicWeightFiltrationProof`](CyclicWeightFiltrationProof.md), Lie
image uniqueness in
[`RepresentedLieUniqueness`](RepresentedLieUniqueness.md), and the
inversion, symmetry and pair-uniqueness interfaces in
[`RootInversionCover`](RootInversionCover.md),
[`RootFactorPairSymmetry`](RootFactorPairSymmetry.md) and
[`RootFactorPairConsequences`](RootFactorPairConsequences.md).
It introduces no new external structural assertion.

`HasNoHigherRoots i a` packages the recurring hypothesis: for every
natural number `n ≥ 2`, the character `n • a` is not in `relativeRoots i`.
It asserts nothing about `a` itself or about the negative ray. The results
below use this predicate on the side or sides they require.

`semigroupSubgroup_eq_bot_of_ambientWeights_vanish` treats an arbitrary
automorphic split-torus action on an affine group locally of finite type.
If its semigroup selects no ambient tangent weight, its generated
semigroup subgroup is the identity. For each smooth connected stable
generator, the published support/tangent equivalence places its tangent
image in the semigroup weight span, which is zero. The identity subgroup
is contained in that generator and has the same actual Lie image.
Published Lie image uniqueness therefore makes each generator the
identity; the universal property of the generated subgroup proves the
claim. This argument needs no representability or general realization
theorem for the generated subgroup itself.

`weightFiltration_two_eq_bot_of_noHigherRoots` applies this vanishing
argument to the second cyclic tail for conjugation. Its characters are
precisely the multiples `n • a` for `n ≥ 2`; their nonzero ambient tangent
weights would be actual relative roots and contradict the hypothesis.

`isInversionPoint_of_noHigherRoots` identifies the first cyclic tail with
the actual root subgroup using the published comparison theorem. That
root subgroup has a smooth connected closed representative. Published
cyclic filtration gives an equivariant vector quotient of this first
tail whose kernel is the second tail. Since the latter is the identity,
the quotient is monomorphic on the required point functors. A torus point
with character value `-1` acts by inversion in the vector coordinates and
therefore in the actual root subgroup. This uses no surjectivity on
rational points.

`hasFpqcInversionPoint_of_noHigherRoots_actual` pulls back the actual
character map along `-1` using `RootInversionCover`. The resulting fpqc
cover has a common torus point whose values under both `a` and `-a` are
`-1`, including in characteristic two. The preceding result supplies
inversion on both actual root subgroups. All cyclic structure inputs are
discharged by the published proofs.

`HasFpqcInversionPoint.hasEqualOppositeFactors` needs only the common
local inversion point, splitness and the monomorphic torus map. For a
supplied pair of a nonidentity rational root point, the reversed inverse
pair exists by group inversion. `IsOppositeFactorPair.eq` supplies its
rational uniqueness at the inverse point. The symmetry helper compares
it with the same-order inverse pair obtained by fpqc descent of
normalization, proving equality of the original factors. Existence of
pairs for arbitrary root points is not used in this comparison.

`IsOppositeFactorPair.nonmultipliable_consequences_of_fpqcInversion`
combines that universal equality with the automatic root flip and
nonidentity of the factors. The symmetry helper gives
`p.1 = m⁻¹ * x * m`, where `m = p.1 * x * p.2`. Equal factors ensure that
the same local torus point inverts `m`: inversion reverses the three
factors, and their outside factors coincide. The square helper then
descends local torus-image membership to
`m * m ∈ (rationalPoints.map i).range`, the actual rational torus image.
The final theorem
`IsOppositeFactorPair.nonmultipliable_consequences_of_noHigherRoots`
supplies the required local inversion from the cyclic geometry above.

The module retains absence of all higher multiples on both sides. It
does not derive that absence from the single hypothesis that `2 • a` is
not a root, and it does not construct an opposite pair. Those remain
obligations of `RootRankOneFactorizationStatement`; this auxiliary
contribution does not prove that target.
