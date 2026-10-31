# Symmetry of Poincaré slices at a point

Module `Langlands.AlgebraicGeometry.Picard.PoincareSliceSymmetry`.

## Definition

`Langlands.AbelianScheme.PoincareSliceSymmetric A hA f t : Prop`, for an abelian scheme
`A` over `S` with a dual scheme (`hA : HasDualScheme A`), a morphism
`f : A.X ⟶ dualScheme A hA` and a point `t : T ⟶ A.X` with `T : Over S`.

Write `Y = T ×_S A` (the object `relativeOver A T`), `τ = relativeFst A T ≫ t : Y ⟶ A`
for the point `t` read on `Y`, and `a = relativeSnd A T : Y ⟶ A` for the
second coordinate. Let `P` be the line bundle underlying the Poincaré family
`poincareFamily A hA` on `A^∨ ×_S A` (parameter first). The proposition says that the
two line bundles

- `(f ∘ τ, a)^* P`, i.e. `P(f(t), a)`, and
- `(f ∘ a, τ)^* P`, i.e. `P(f(a), t)`,

on `Y` are isomorphic (`Nonempty` of an isomorphism of `LineBundle`s). The pair maps are
`pairOver A _ _` from `SquareTheorem`, giving a morphism `Y ⟶ A^∨ ×_S A` over `S`.

## Provenance and purpose

This is an internal auxiliary notion for the proof of
`Langlands.AbelianScheme.PolarizationDiagonalMumfordStatement`
(Mumford, Fogarty, Kirwan, *Geometric Invariant Theory*, 3rd ed., Prop. 6.10). If `f`
is the Mumford map `Λ(L)` of a line bundle, the symmetry holds because the Mumford
bundle `m^*L ⊗ p_1^*L^{-1} ⊗ p_2^*L^{-1}` is symmetric in its two factors; the proof
uses this at field-valued points after base change, where a polarization becomes a
Mumford map.

## Related results (other modules)

- `poincareSliceSymmetric_mumfordSchemeMap` (module `PoincarePointClasses`): a Mumford map
  has symmetric Poincaré slices at every point.
- `poincareSliceSymmetric_of_baseChange` (module `PoincareSliceSymmetryBaseChange`): the
  property descends along a change of base `S' ⟶ S`.
- `comp_mumfordSchemeMap_poincareDiagonal` (module `PoincareDiagonalClasses`) uses the
  property at a point over a one-point scheme.
