# Bounded norms for finite products of Weil restrictions over K

Authors: Worker 1587, using the tensor-coordinate kernel comparisons by Worker 706.

Let `F` be a nonarchimedean local field, let `K = UnramifiedClosure F`,
and let `L/K` be a finite Galois intermediate extension inside the fixed
separable closure of `F`. For any finite family `E i` of intermediate fields
of `L/K`, put `W = Res_{(∏ i, E i)/K} Gm`, using the actual published
`WeilGm.commGroupScheme`. All fields and the family retain the arbitrary
universe `u`; the family may be empty.

`weilProductBoundedNormLift F L E` assigns to every point of the
`fixedFieldValuation F` character kernel of `W` a point of the
`intermediateValuation F L` character kernel of the actual base change
`W_L`. Its actual rational norm is the original point, by
`rationalNorm_weilProductBoundedNormLift`. Thus the bounded rational norm
is surjective, and `weilProduct_torusNormIwahori_eq_characterValuationKernel`
identifies the norm Iwahori subgroup with the bounded subgroup in this case.

The construction reads a ground point as a unit of the finite product
algebra, then reads its factors using `MulEquiv.piUnits`. The finite-Galois
character-kernel ascent and embedding-coordinate criterion show that each
factor has valuation one after inclusion in `L`.
`intermediateUnitNormLift` supplies a valuation-one unit of `L` whose
relative norm to that factor is the prescribed unit. The definition
`weilProductUnitNormLifts` records these scalar lifts.

The actual extension point is `inclusionSupportedPoint` with these units:
it has the chosen lift at each inclusion embedding and value one at every
other embedding. The general helper
`inclusionSupportedPoint_mem_characterValuationKernel` applies the product
coordinate criterion and checks these two possibilities, proving that the
point is bounded. The norm-coordinate formula
`rationalNorm_inclusionSupportedPoint` and the scalar norm-lift law identify
every factor of its norm with the prescribed factor. Injectivity of the
actual point-to-unit equivalence and the product-unit equivalence gives the
point equality. The reverse subgroup inclusion is the existing theorem that
norms preserve unit character values for compatible invariant valuations.

Provenance: an internal composition of the published scalar unit-norm theorem,
actual Weil-restriction tensor-point and rational-norm constructions, and
character-kernel coordinate comparisons. This proves the finite-product
Weil-restriction case only. The passage from an arbitrary `IsInducedTorus`
to this form remains a separate structural prerequisite; this module does
not claim the full `InducedTorusIwahoriStatement`.
