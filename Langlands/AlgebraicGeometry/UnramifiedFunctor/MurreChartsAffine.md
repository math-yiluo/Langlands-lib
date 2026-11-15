# Affine test objects over `Spec R`

Module `Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreChartsAffine`, namespace
`Langlands.AlgebraicGeometry.UnramifiedFunctor.Charts`. Bookkeeping for the chart
construction in `MurreCharts`, over the base `Spec R` with `R : CommRingCat`.

## Contents

* `ovR R T`: an `R`-algebra `T` as the object `Spec T ⟶ Spec R` of `Over (Spec R)`;
  `homR φ : ovR R T' ⟶ ovR R T` for an `R`-algebra map `φ : T → T'`; `homR_left`,
  `homR_comp` (contravariant functoriality), `map_homR_map_homR`.
* `towerIso A T`: for `R → A → T`, the object `Spec T ⟶ Spec A ⟶ Spec R` is isomorphic to
  `ovR R T` (identity on `Spec T`). It translates between the objects used in
  `MurreChartsLocalization` (via `BaseChange.specOver`) and `ovR`.
* `awayOver`, `toLocOver`, `resAway`, `toLocOver_comp`, `awayOver_comp`,
  `map_toLocOver_resAway`, `map_awayOver_resAway`: the morphisms of the diagram of
  `MurreChartsLocalization` written as explicit `Over.homMk`, and their compatibility with
  restriction from `Spec A`.
* `toLocₐ M B a : A[1/a] →ₐ[R] B` for `B = M⁻¹A` and `a ∈ M`.
* `exists_away_of_isLocalization` ((F1a), (F2)): every element of `F(Spec B)`, `B = M⁻¹A`,
  is the restriction of an element of `F(Spec A[1/a])` for some `a ∈ M`.
* `exists_away_eq_of_eq` ((F1a), (F2)): two elements of `F(Spec A)` with the same restriction
  to `Spec B` have the same restriction to some `Spec A[1/a]`, `a ∈ M`.
* `map_injective_of_field` ((F1b)): for fields `K` (an `R`-algebra) and `L`, restriction
  along any morphism `Spec L ⟶ Spec K` over `Spec R` is injective: the morphism is flat,
  surjective and quasi-compact, so (F1b) gives the sheaf condition for the singleton covering,
  in particular separatedness.
* `awayMapₐ`, `awayMapₐ_comp_toAlgHom`, `homR_awayMapₐ_comp`,
  `isOpenImmersion_homR_awayMapₐ`: for `a ∣ b` the map `Spec A[1/b] ⟶ Spec A[1/a]` is an open
  immersion (its composite with the open immersion `Spec A[1/a] ⟶ Spec A` is the open
  immersion `Spec A[1/b] ⟶ Spec A`; `IsOpenImmersion.of_comp`).
