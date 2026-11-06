# Morphism pullbacks on actual continuous rational-invariant functions

This internal construction works over an arbitrary-universe number field
`F`. Its groups are actual affine group schemes over `Spec F`, and its
function spaces are the existing `ContinuousRationalFunctions F G`.
These are complex-valued continuous functions on the actual adelic point
group, invariant under left multiplication by actual rational points.

For every group-scheme morphism `φ : G ⟶ H`, `continuousPullback F φ`
is the complex-linear map from the target group's function space to the
source group's function space given by
`f ↦ (x ↦ f (AdelicGroupPoints.map F G H φ x))`.
The adelic point map is the existing continuous group homomorphism
induced by the same scheme morphism on points over the full adele ring.
Its compatibility with principal rational points proves the required
left invariance. Continuity follows by composition, and linearity is
pointwise. There is no injectivity or surjectivity assumption on `φ`.

`continuousPullback_id` and `continuousPullback_comp` establish the
identity and contravariant composition laws on these original carriers.
Their proofs use the identity and composition laws of the coefficient
point maps. The composition formula reads
`(φ ≫ ψ)⁎ f = φ⁎ (ψ⁎ f)`.

The right action has the positive convention `R(g)f(x) = f(x * g)`.
`continuousPullback_rightAction` proves
`φ⁎ (R(φ(g)) f) = R(g) (φ⁎ f)` directly from preservation of
multiplication by the adelic point map.
`continuousPullbackIntertwiningMap` bundles this equality as an
intertwining complex-linear map: the target group's representation is
restricted along the actual adelic point homomorphism, and the codomain
is the source group's original representation.

For an actual group-scheme isomorphism `e : G ≅ H`,
`continuousPullbackEquiv F e` is a complex-linear equivalence from the
function space for `H` to that for `G`. Its inverse is pullback along
`e.inv`; the two inverse identities follow from contravariant composition
and the identity law. The two evaluation lemmas record the values of the
equivalence and its inverse at actual adelic points.

The provenance is internal. The file combines the published
`GroupSchemeAmbient` function carriers and actions with the actual point
maps and rational naturality from `AdelicGroupNormOneFunctorial`; it
attributes no new result to external literature. It assumes affineness
to use the existing topology and makes no reductivity, finite-type,
measure, growth or finite-level assumption. It does not assert that
arbitrary morphisms preserve constant terms or cuspidality. Transport
of subgroup quotients, intrinsic measures and convergent periods remains
separate work.
