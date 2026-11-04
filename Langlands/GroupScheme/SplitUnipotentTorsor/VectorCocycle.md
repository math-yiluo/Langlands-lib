# Cocycles valued in a one-dimensional vector group

Module: `Langlands.GroupScheme.SplitUnipotentTorsor.VectorCocycle`.

This module supplies the vector-group step in the proof of
`Langlands.GroupScheme.SplitUnipotentAffineTorsorStatement`: over an affine base,
every natural cocycle valued in the base change of a one-dimensional vector group
is trivial. It is internal to that proof. Mathematically it is the classical fact
`H¹_fpqc(Spec A, G_a) = 0` for an affine scheme `Spec A`, here proved for one affine
flat surjective cover at a time. A cocycle is `Langlands.GroupScheme.Cocycle` from
`Langlands.GroupScheme.TorsorCocycle`: a natural group-valued function on pairs of
points of the cover over every test scheme.

## Declarations

- `VectorCocycle.baseChangeCoordinates e T Z`: for a family `e` of multiplicative
  equivalences `(W ⟶ V.X) ≃* Multiplicative (Fin n → Γ(W.left, ⊤))` over all
  `W : Over B` and an object `T : Over B`, the induced equivalence on the points over
  `Z : Over T.left` of the base change `(GroupScheme.baseChange T.hom).obj V`. It
  composes the pullback adjunction on points, `baseChangePointsEquiv`, with `e`
  at `Z` viewed over `B`.
- `VectorCocycle.baseChangeCoordinates_comp`: if `e` is natural in the sense used in
  `IsVectorGroupOfDimension` (the coordinates of `b ≫ x` are the pullbacks along
  `b.left` of the coordinates of `x`), then so is `baseChangeCoordinates e T` for
  every `t : Z' ⟶ Z` in `Over T.left`.
- `Cocycle.isTrivial_of_isVectorGroupOfDimension_one`: let `V` be a group scheme over
  any scheme `B` with `IsVectorGroupOfDimension V 1`. Let `T : Over B` have affine
  total space, and let `U : Over T.left` be flat and surjective with affine total
  space. Then every cocycle on `U` with values in `(GroupScheme.baseChange T.hom).obj V`
  is trivial: it is `(a, b) ↦ f(a) f(b)⁻¹` for one point `f : U ⟶ V_T.X`.

## Proof

Choose natural coordinates `e` for `V` from `IsVectorGroupOfDimension V 1` and let
`coord = baseChangeCoordinates e T`. The single coordinate of `ξ(a, b)` under `coord`
is a natural additive cocycle `α` valued in global functions
(`Langlands.AlgebraicGeometry.AffineAdditiveCocycle.AddCocycle U`). Naturality
follows from the naturality of `ξ` and `baseChangeCoordinates_comp`. The additive
cocycle identity follows from the multiplicative one because `coord` is a
multiplicative equivalence onto `Multiplicative (Fin 1 → Γ)`.
`AddCocycle.exists_coboundary` (degree-one Amitsur exactness, needing `T.left` and
`U.left` affine and `U.hom` flat and surjective) gives `β ∈ Γ(U.left, ⊤)` with
`α(a, b) = a^*β - b^*β`. Put `f = coord⁻¹(β)`. By `baseChangeCoordinates_comp`, the
coordinate of `a ≫ f` is `a^*β`, so `ξ(a, b)` and `(a ≫ f) * (b ≫ f)⁻¹` have the same
coordinate. They are equal because `coord` is injective and `Fin 1` has a single
element.
