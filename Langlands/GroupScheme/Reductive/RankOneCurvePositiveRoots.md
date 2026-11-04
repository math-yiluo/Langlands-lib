# Positive roots from a prescribed homogeneous quotient curve

This internal assembly connects the actual signed noncontainment construction,
the canonical dynamic unipotent bound on a homogeneous quotient curve, and the
integral normalizer symmetrization. It works over an algebraically closed field
in universe `u`, in every characteristic.

`SignedCurveUnipotentData` stores a selected actual cocharacter equal to `ν` or
`-ν`, its all-test dynamic noncontainment in a specified subgroup, and
`CurveUnipotentData` for that same direction. The latter contains an actual
smooth connected affine unipotent representative, its closed inclusion, a
moving dominant quasi-compact orbit on the quotient, and Lie dimension at most
one. `finrank_tangent_le_one_or_neg` uses the sign equality and represented
tangent comparison to bound one of the two intrinsic signed tangent dimensions.

`signedCurveUnipotentData` takes a pseudo-reductive ambient group `G`, a proper
closed solvable subgroup `b : B ⟶ G`, a split torus mapping to `B`, and a
cocharacter. Its geometric input is an actual quasi-compact smooth surjective
quotient with exact all-test right-coset fibers, separated target, and
topological Krull dimension at most one. It also requires all-test containment
of the dynamic centralizer in `B` and an explicit proof of
`AlgClosedReductiveNormalSolvableTorusStatement`. Smoothness of `B` is derived
from the exact smooth quotient and affineness from its closed inclusion.
`Dynamic.noncontainedSignedDirection` selects a dynamic unipotent sign outside
`B`, and `curveUnipotentData` constructs its actual small representative and
moving orbit. The caller supplies neither the sign nor a tangent bound.

`positive_roots_eq_of_rankOne_curve_quotient` specializes this construction to
a connected reductive group, a split maximal torus, and pairwise integrally
dependent actual roots. A supplied normalizer point has nonidentity class in
the actual quotient `N(k)/Z(k)`. The construction is applied to the integral
symmetrization `η = ν - wν`, so centralizer containment is required for this
specific `η`. The selected sign bounds the tangent dimension of `U(η)` or
`U(-η)`. The signed normalizer tangent bridge identifies their dimensions by
actual conjugation and uses integer root-pairing doubling to give equality
of any two actual roots positive for the original `ν`. No division by two
or characteristic restriction occurs.

The provenance is internal: Worker 1547 combines the signed noncontainment
and canonical curve constructions with Worker 1549's signed tangent bridge.
Worker 317 contributed the included earlier signed-dimension and unipotent
orbit-bound dependencies. The proof uses their stated conditional results;
it asserts no additional external structural theorem.

The normal-solvable-torus theorem, existence of the proper subgroup and its
quotient curve, symmetrized-centralizer containment, and the nonidentity
normalizer class remain explicit obligations. This helper does not prove the
unconditional `RankOnePositiveRootUniquenessStatement`.
