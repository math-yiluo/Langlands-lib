# Compact finiteness of genuine automorphic enveloping derivatives

The theorem `Langlands.Automorphic.automorphicDifferentialInfiniteFinite`
proves the published `AutomorphicDifferentialInfiniteFiniteStatement K n`
for every number field `K : Type u` and every natural rank `n`, including zero.
For each actual automorphic form `f` and each element `a` of the complex
universal enveloping algebra, the continuous function underlying
`finiteSmoothEnvelopingAction K n a f.val` has finite-dimensional complex
translate span under `standardInfiniteCompact K n`.

The theorem has no additional covariance or preservation assumption. Its
unapplied closing example checks the full telescope, including the arbitrary
universe and rank. All differential and translation operators are the published
concrete operators on the actual adelic matrix group.

## A finite-dimensional bound for differentiated orbits

The general helper
`Langlands.FiniteVectors.isFiniteVector_bilinear_of_covariance` works over any
field `k`, any monoid `G`, any representation `ρ` on a `k`-vector space `V`,
and any finite-dimensional direction space `E`. Let
`D : E →ₗ[k] Module.End k V` be a linear family of operators. For a fixed
direction `X : E` and a finite vector `v`, assume that for each `g : G` there
is some `Y : E` with

`ρ g (D X v) = D Y (ρ g v)`.

Let `S = orbitSpan ρ v`. The bilinear evaluation map on `E × S` induces
`T : E ⊗[k] S →ₗ[k] V`. Both tensor factors are finite dimensional, so the
range of `T` is finite dimensional. The assumed equality expresses each
translate of `D X v` as the image under `T` of the pure tensor consisting of
`Y` and the vector `ρ g v` in `S`. Therefore the orbit span of `D X v` is a
subspace of this finite-dimensional range and is finite dimensional. Only this
general helper takes a covariance hypothesis; the concrete application below
discharges it with a published theorem.

## The actual subgroup action and finite-vector predicate

In namespace `Langlands.Automorphic`,
`finiteSmoothInfiniteSubgroupRightAction K n U` restricts the actual
`finiteSmoothRightAction` to an arbitrary subgroup `U` of
`InfiniteAdelicGL K n` through `AdelicGL.ofInfinite`. Its value at `g : U`
is the same adelic right translation by the image of `g.val`.

`finiteSmoothInfiniteSubgroupInclusion` is the subtype inclusion into
`ContinuousRationalFunctions K n`, as an intertwining map to the published
`infiniteSubgroupRightAction`. The intertwining equality is definitional,
and the inclusion is injective. Consequently the existing
`FiniteVectors.isFiniteVector_map_iff` gives
`isInfiniteFinite_iff_finiteSmoothVector`: the published predicate
`IsInfiniteFinite K n U f.val` is equivalent to finite-vector membership
for this actual action on `FiniteSmoothRationalFunctions K n`.
These constructions only restrict and forget structure from existing actions.

## Lie generators

`finiteSmoothComplexDifferential` composes the published complex-linear
`envelopingGenerator` with the algebra action `finiteSmoothEnvelopingAction`.
Thus it is the linear family of differential operators parameterized by the
complexified real matrix Lie algebra. The private helper
`complexLieAlgebra_finite` obtains real finite dimensionality from
`realLieAlgebraToMatrix` and finite dimensionality of the actual matrix space;
scalar extension then gives finite dimensionality of its complexification.

`isFiniteVector_realDifferential` applies the general bound with this
complex direction space. For `g : U` and a real direction `X`, choose the
complexification of the real direction corresponding to

`C(g.val) * M(X) * C(g.val⁻¹)`,

where `C = archimedeanGLCoordinates K n` and
`M = ArchimedeanGL.realLieAlgebraToMatrix K n`. The imported theorem
`finiteSmoothRealDifferentialCovariance` from
`Langlands.Automorphic.RealDifferentialCovarianceProof` gives precisely the
required equality between the translate of the derivative and this conjugated
derivative of the translate. That theorem concerns the actual finite-smooth
space and the genuine enveloping action, so no new analytical hypothesis is
introduced here.

`isFiniteVector_complexDifferential` extends this conclusion to every complex
Lie direction by induction on the tensor product defining complexification.
A pure tensor `z ⊗ X` is `z` times the complexification of `X`; linearity of
the generator and action reduces that case to scalar closure of finite vectors.
The sum case uses their additive closure.

## Enveloping elements and the final specialization

`isFiniteVector_envelopingAction` first lifts an arbitrary enveloping element
to the tensor algebra using surjectivity of its quotient map. Tensor-algebra
induction then handles scalars, Lie generators, products, and sums. Scalars
use scalar closure; generators use the preceding theorem; products use
composition of the two operators and the induction hypotheses; sums use
additive closure. The induction generalizes over the input function, so in
the product case the first hypothesis applies to the output of the second.
This proves preservation of finite vectors for every subgroup `U` of the
actual infinite group and every actual enveloping element.

Finally, `automorphicDifferentialInfiniteFinite` specializes `U` to
`standardInfiniteCompact K n`. The published characterization
`mem_automorphicSubrepresentation` extracts the input compact-finiteness
condition from membership of the actual automorphic form. The faithful
inclusion transfers that condition to the finite-smooth representation, the
enveloping theorem preserves it, and the same equivalence transfers the
result back to the published continuous-function predicate.

## Provenance and scope

This is an internal algebraic proof of the published target in
`Langlands.Automorphic.PreservationStatement`. Its source context is Borel and
Jacquet, *Automorphic forms and automorphic representations*, Corvallis Part I
(1979): section 1.5(1), printed p. 190 (one-based PDF p. 185), identifies compact
finiteness; sections 2.1–2.2, printed pp. 192–193 (PDF pp. 187–188), discuss the
archimedean automorphic module; sections 4.2–4.3, printed p. 195 (PDF p. 190),
give the adelic conditions and passage to arithmetic quotients. The original
source and the cross-reference slips in section 2.2 are documented in the
published statement's Markdown. The registered source is
`borel-jacquet-1979-automorphic`, the file
`/home/taskhub/central-library/Borel-Casselman--Automorphic Forms, Representations and L-Functions (Corvallis)--1979/Part I.pdf`,
with SHA256 `3b9fe0145da81d870ef8967be83635cd440a2581fe043e64e63324e22dec4db5`.

The tensor-product image argument is derived here from elementary linear
algebra and the independently proved real-generator covariance. It uses no
compactness argument or PBW theorem: the stronger intermediate result holds
for every infinite subgroup. The final theorem proves only preservation of
compact finiteness, not growth, admissibility, or the full automorphic
preservation conjunction. Center finiteness and growth of the input are not
needed for this component. Rank zero is covered uniformly by the same
finite-dimensional and algebraic constructions. The proof uses default
heartbeats and only the standard axioms `propext`, `Classical.choice`, and
`Quot.sound`.

The three local additive-group helper instances have explicit module-specific
names, allowing this proof to be imported together with the actual cuspidal
and operator-core constructions without collisions between generated
declaration names. Their types and bodies remain the standard submodule
additive-group structures.
