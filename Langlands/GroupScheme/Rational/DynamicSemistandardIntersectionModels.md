# Actual models for semistandard intersections

This internal construction assembles the existing affine dynamic representatives
into compatible actual closed models of the three intersection functors inside
a representative of the first centralizer. It preserves arbitrary commutative
base rings, universes and every test scheme for the construction. No nesting is
assumed. The final structural reductions are over arbitrary fields.

`SubgroupFunctor.ClosedDecompositionModel P L U` contains three actual group
schemes, their maps into the ambient group and into the first model, exact
all-test representation identities, and closedness of the three inclusions.
Multiplication with the Levi factor first is an isomorphism of schemes. On every
test, the two factors are contained in `P`, the identity-limit factor is normal,
the factors are complementary inside `P`, and `P = L * U` in that order.
This data does not assert parabolicity, reductivity or a geometric radical.

`Dynamic.unipotentToParabolic` lifts the inclusion of identity-limit points
through any represented dynamic parabolic by the published Yoneda construction.
Its composite with the parabolic inclusion is the original unipotent inclusion.
`affineDecompositionModel` uses the published affine dynamic schemes, this map,
and the published centralizer inclusion. Closedness follows by cancellation
through the closed parabolic inclusion. The multiplication isomorphism is the
published `Dynamic.isIso_subgroupMultiplication` from `Rational.LeviMultiplication`.
Normality and complementarity are the published dynamic limit results. The
ordered product follows directly from a limit `l` of `g`: `l` is in the
centralizer, `l⁻¹ * g` has identity limit, and `g = l * (l⁻¹ * g)`.

`intersectionCocharacter` composes the second cocharacter with the published
factorization of the common commutative group through the first centralizer.
Its composite with the first centralizer inclusion is the original second
cocharacter. The three closed-subgroup comparison theorems identify its dynamic
functors exactly with the three comaps. `commonTorusIntersectionModel` reindexes
the chosen affine models along those equalities. It assumes that the first
centralizer representative is affine; for a closed representative in an affine
ambient group, `IsClosedSubgroup.isAffineHom` supplies affineness over the base.

The supporting structural assembly theorem converts such a model into the
existing `IsParabolicWithLeviAndRadical` predicate when its actual parabolicity,
Levi reductivity and full geometric radical identification have been proved.
`isParabolicWithLeviAndRadical_of_structural` applies the three existing
proposition targets `ParabolicDynamicStatement`,
`DynamicCentralizerReductiveStatement`, and
`DynamicGeometricUnipotentRadicalStatement` to discharge those conditions.
`dynamicSemistandardIntersection_of_structural` then proves the exact original
semistandard proposition conditionally on those three structural targets,
using the published common-torus products and maximal split torus lift.

The source of this unit is the existing actual dynamic definitions,
representation universal properties, closed-subgroup comparison and limit
theorems; no external theorem or new geometric assertion is imported as fact.
The three structural targets and the unconditional original semistandard theorem
remain unproved by this module.
