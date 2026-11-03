# Finite Krull dimension of affine group coordinates

This internal construction supplies a natural-number upper bound for the Krull
dimension of the actual global coordinate ring of an affine group scheme locally
of finite type over a field. It uses the existing group-scheme objects and
Mathlib's finite-type and Krull-dimension results. It asserts no new external
literature theorem.

For a finite-type commutative algebra over a field,
the published
`Langlands.AlgebraicGeometry.Modules.SerreVanishing.exists_ringKrullDim_le`
takes a surjection from a polynomial
ring in finitely many variables. Surjectivity bounds the target's Krull
dimension by that of the polynomial ring; Mathlib computes the latter as the
number of variables. The bound remains valid for the zero algebra.
`finiteRingKrullDim_of_finiteType` additionally requires a nonzero algebra,
because `FiniteRingKrullDim` includes nonemptiness of the prime spectrum.

For an actual group scheme `G` over `Spec k`, `globalCoordinateAlgebraMap`
composes the scalar identification `k ≅ Γ(Spec k, ⊤)` with the map on global
sections of the structure morphism. When `G` is affine and its structure morphism
is locally of finite type, `globalCoordinateAlgebraMap_finiteType` proves this
ring map is finite type. The argument uses the affine ring-map characterization
of locally finite type and finite type of a ring isomorphism.

`globalCoordinates_nontrivial` pulls global functions back along the identity
section and then identifies the resulting base coordinates with `k`. A unital
ring map to the nonzero field forces the global coordinate ring to be nonzero;
this does not require affineness or smoothness.

`coordinateKrullDimensionBound G` chooses the natural-number bound produced by
`globalCoordinates_exists_dimensionBound`.
`ringKrullDim_globalCoordinates_le` proves its upper-bound property, and
`globalCoordinates_finiteRingKrullDim` gives
`FiniteRingKrullDim Γ(G.X.left, ⊤)`. Consumers may install this last theorem as a
local instance. The construction allows every field, all characteristics and
imperfect fields; it assumes neither connectedness nor smoothness nor
solvability. It supplies only a dimension prerequisite: no maximal-torus
extension or conjugacy theorem is claimed here.
