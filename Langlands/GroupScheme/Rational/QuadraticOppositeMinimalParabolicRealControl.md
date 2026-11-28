# Real-controlled reduction to a quadratic opposite minimal parabolic Levi subgroup

The module `Langlands.GroupScheme.Rational.QuadraticOppositeMinimalParabolicRealControl`
proves `IsQuadraticOppositeMinimalParabolicLevi.exists_realLocallyTrivialRepresentative`, the
analogue for minimal parabolic subgroups of
`IsQuadraticOppositeBorelTorus.exists_realLocallyTrivialRepresentative` (module
[`QuadraticOppositeBorelRealControl`](QuadraticOppositeBorelRealControl.md)).

## Statement

Let `F` be a number field, `Q/F` a finite Galois extension, `G` a connected reductive group
over `F`, and `t : C ⟶ G` with `IsQuadraticOppositeMinimalParabolicLevi Q t`. Every cocycle
`ξ` of `G` on `Spec Q → Spec F` whose pullback to `Spec (F_v ⊗_F Q) → Spec F_v` is trivial at
every real place `v` of `F` is cohomologous to `δ.map t` for a cocycle `δ` of `C` on the same
cover whose pullback is again trivial at every real place.

## Proof

The module repeats the argument of `QuadraticOppositeBorelRealControl` with the Levi subgroup
`C` in place of the torus; its private lemmas are restated here for a general middle group.

- `C` is connected reductive over `F`: `C_Q` is connected reductive as a rational Levi
  subgroup, and connected reductivity descends along field extensions
  (`IsConnectedReductive.of_fieldExtension`).
- `IsQuadraticOppositeMinimalParabolicLevi.exists_dynamicData` (module
  [`QuadraticOppositeMinimalParabolicDynamic`](QuadraticOppositeMinimalParabolicDynamic.md))
  gives `σ ≠ 1` and a cocharacter `χ` of `G_Q` with `Z(χ) = C_Q` and `σ(U(χ)) = U(-χ)`; the
  cell `U(χ) × C_Q × U(-χ) → G_Q` is an open immersion
  (`Dynamic.isOpenImmersion_leviOppositeCell`).
- At a real place `v` of `F` with a complex place `w` of `Q` above it, with `K = F_v` and
  `M = Q_w`, `exists_relativeCoboundaryNeighborhood_of_isConnectedReductive` (module
  [`QuadraticReductiveCoboundaryNeighborhood`](QuadraticReductiveCoboundaryNeighborhood.md))
  supplies the open neighbourhood of `1` in `C(M)` required by
  `GaloisCocycle.exists_localLeviCellControl` (module
  [`QuadraticLeviCellLocalControl`](QuadraticLeviCellLocalControl.md)). This gives an open set
  of `G(Q_w)` such that twisting `ξ` by a rational point in it puts its value at `σ` in the
  cell, with middle coordinate trivializing over `F_v` every cocycle of `C` with that value.
- Weak approximation at the complex places of `Q` above real places of `F`
  (`exists_reductivePoint_mem_complexCompletion_opens`) gives one `f ∈ G(Q)` in all these open
  sets; if there are no such places, the density of twisted Galois values puts a twisted value
  in the cell. At a real place of `F` with a real place of `Q` above it, the pulled-back cover
  has a section and every cocycle is trivial there.
- `GaloisCocycle.exists_leviCocycle_of_leviOppositeCell` (module
  [`QuadraticLeviCellCocycleLift`](QuadraticLeviCellCocycleLift.md)) turns the cell
  coordinates of the twisted value into a cocycle `δ` of `C` with `δ.map t` cohomologous to
  `ξ` and value at `σ` the middle coordinate, which is therefore trivial at the real places.

## Source

V. Platonov and A. Rapinchuk, *Algebraic Groups and Number Theory* (Academic Press, 1994),
source ID `platonov-rapinchuk-1994-algebraic-groups-number-theory`, Lemma 6.28' (printed
p. 383), whose proof follows that of Lemma 6.28 (printed pp. 369–370) with the generalized
decomposition of Borel–Tits, §5.
