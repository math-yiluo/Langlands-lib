# Transition maps between Harris's `C_m^{•,H}` for a change of `H`

Author: Worker 61. Built on `Langlands.Cohomology.DivisibleSystem.StandardMap`
(`groupStandardTotalSystemMap`, `groupStandardTotalSystemMap_tower_app_comp`,
the normalized fiber sum `groupStandardMap`) and
`Langlands.Cohomology.DivisibleSystem.InvariantComparison` (`extendMapIso`,
`extendMapIso_hom_naturality`, `mapHom`, `extendSystemComparison`,
`Rep.quotientInflation`, `inflateQuotientInvariantsComplexesHom`,
`inflatedQuotientInvariantsTotalSystem`,
`quotientInvariantsTotalSystemToRepExtend`,
`quasiIso_quotientInvariantsTotalSystemToRepExtend`), and through them on
`…InvariantTotal` (`quotientInvariantsTotalSystem`), `…TotalComparison`
(`standardTotalSystemToExtend`, `groupStandardTotalSystemToExtend`,
`quotientInvariantsTotalSystemToExtend`, `columnComparisonF`,
`columnComparisonF_naturality`), `…Total` (`totalSystemMap`,
`upFinTotalFunctor`, `standardTotalSystem`), `…StandardResolution`
(`standardResolution`, `standardResolutionAugmentation`, `indResBot`,
`indResBotCounit`), `…Invariants` (`smoothQuotientInvariants`,
`quotientInvariantsComplexes`, `quotientInvariantsComplexesInclusion`,
`toRepComplexes`), `…Sections` (`mapComplexes`), `…ProPInvariants`
(`IsProPSubgroup`), the base module `DivisibleSystem` (`map`,
`mapFunctor`, `extendSystem`, `hom_ext`), `Langlands.Cohomology.DerivedPlus`
(`extendXMapIso`) and Worker 3's
`Langlands.Cohomology.ProPInvariants.Statement`
(`ProPInvariantSubcomplexStatement`, used only as a hypothesis). From
Mathlib it uses `HomologicalComplex.extend`, `HomologicalComplex.extendMap`,
`Functor.mapHomologicalComplexCompIso`, `QuotientGroup.map`,
`Rep.quotientToInvariantsFunctor`, `Rep.resFunctor` and quasi-isomorphisms.

Everything is in the namespace `Langlands.Cohomology`; the declarations of
the sections "Systems" and "The transition morphism" below are in
`Langlands.Cohomology.DivisibleSystem`.

Notation: composition `f ≫ g` is `f` followed by `g`. For normal subgroups
`H' ≤ H` of `G`, `π : G ⧸ H' →* G ⧸ H` is the projection, `Res_π` is
restriction along `π` (`Rep.resFunctor π`) and `Inf_H` is inflation along
`G ⟶ G ⧸ H` (`Rep.quotientInflation R H`). For a smooth representation `V`
of `G`, `V^H` is its `H`-invariants as a representation of `G ⧸ H` (the
Library's `smoothQuotientInvariants R H`, Mathlib's
`Rep.quotientToInvariantsFunctor`). For an `ℓ`-divisible system `K` of
`ℕ`-graded complexes of smooth representations of `G`, `K^H` is
`K.quotientInvariantsComplexes H hK` (the invariants in every degree of every
level) and `C^{•,H}` is `quotientInvariantsTotalSystem N K H hK`, the total
complexes (rows `q < N`) of the standard resolutions of `K^H` along
`Ind_1^{G⧸H} Res_1^{G⧸H}`. The hypotheses `hK`, `hK'` say that the
projections of `K` stay epimorphisms on `H`-invariants and on
`H'`-invariants.

## Extension to `ℤ` and composite functors

`e` is an embedding of complex shapes, `C`, `D`, `E` have zero morphisms and
zero objects, `F₁ : C ⥤ D`, `F₂ : D ⥤ E`, `F₃ : C ⥤ E` preserve zero
morphisms, and `α : F₁ ⋙ F₂ ≅ F₃`. `extendMapIso e F K` is the
InvariantComparison module's identification of `F` of `K` extended along `e`
with `F K` extended along `e`.

- `extendXMapIso_inv_comp_comp α K j`: the component at the index `j` of
  the extension (Mathlib's `extend.X K j`) of the next lemma. For
  `j = none` the target is a zero object, so the two sides agree. For
  `j = some i` the three extension comparisons `extendXMapIso` are
  identities (the one under `F₂` up to `F₂.map_id`), and both sides reduce
  to the same component `α.inv.app (K.X i)` of the natural isomorphism. This
  component is arbitrary and need not be an identity.
- `extendMapIso_hom_comp e α K`: the comparisons `extendMapIso` for `F₁`,
  `F₂` and `F₃` are compatible with `α`: `α.inv` on `K` extended,
  followed by `F₂` of the comparison for `F₁` and the comparison for `F₂`
  (on `F₁ K`), equals the comparison for `F₃` followed by the extension of
  `α.inv` on `K`.
- `extendComparison_comp_eq t g t₁ s t₂ c₀ u' u h₁ h₂ h₃`: an abstract form
  of the compatibility proved in the last section. Given
  `t : T ⟶ X.extend e`, `g : F₁ T ⟶ T₁`, `t₁ : T₁ ⟶ (F₁ X).extend e`,
  `s : T₁ ⟶ T₂`, `t₂ : T₂ ⟶ X'.extend e`, `c₀ : F₁ X ⟶ X'`,
  `u' : F₂ X' ⟶ Y` and `u : F₃ X ⟶ Y` with
  `h₁ : g ≫ t₁ = F₁ t ≫ (extendMapIso e F₁ X).hom`,
  `h₂ : s ≫ t₂ = t₁ ≫ extendMap c₀ e` and
  `h₃ : α.inv ≫ F₂ c₀ ≫ u' = u`, the morphism `α.inv ≫ F₂ (g ≫ s)`
  followed by `F₂ t₂ ≫ (extendMapIso e F₂ X').hom ≫ extendMap u' e` equals
  `F₃ t ≫ (extendMapIso e F₃ X).hom ≫ extendMap u e`. Proof: `h₁` and `h₂`
  give `(g ≫ s) ≫ t₂ = F₁ t ≫ (extendMapIso e F₁ X).hom ≫ extendMap c₀ e`;
  then the naturality of `α.inv` and of `extendMapIso` for `F₂`,
  `extendMapIso_hom_comp` and `h₃`.

## Invariants for a smaller subgroup

`R` is a commutative ring, `H' ≤ H` normal subgroups of a group `G` (the
hypothesis `hHH'`).

- `quotientProjection hHH'`: `π : G ⧸ H' →* G ⧸ H`, Mathlib's
  `QuotientGroup.map` of the identity of `G`; `quotientProjection_mk`
  (`π` of the class of `g` is the class of `g`, `rfl`) and
  `surjective_quotientProjection`.
- `quotientInvariantsChange R hHH'`: the natural transformation
  `(·)^H ⋙ Res_π ⟶ (·)^{H'}` of functors from `Rep R G` to
  `Rep R (G ⧸ H')`, the inclusion of the `H`-invariants into the
  `H'`-invariants (`Submodule.inclusion`). It is `G ⧸ H'`-equivariant
  because both actions are induced by the action of `G`.
- `quotientInflationResIso R hHH'`: `Res_π ⋙ Inf_{H'} ≅ Inf_H`, with
  identity components: both functors restrict along `G ⟶ G ⧸ H`.
- `smoothQuotientInvariantsChange R hHH'` (`G` a topological group):
  `quotientInvariantsChange` precomposed with the forgetful functor from
  smooth representations.

## Systems

- `mapCompHom α T` (`α : F₁ ⋙ F₂ ≅ F₃` of exact functors between abelian
  categories): the morphism of `ℓ`-divisible systems `T.map F₃ ⟶
  (T.map F₁).map F₂` given by `α.inv` at every level
  (`mapCompHom_tower_app`, `rfl`).
- `mapComplexesCompHom K β hΦ hΦ'` (for `β : Φ ⋙ Ψ ⟶ Φ'`, `Φ`, `Φ'` left
  exact, `Ψ` exact): the morphism from `Ψ`, applied degreewise, of
  `K.mapComplexes Φ hΦ` to `K.mapComplexes Φ' hΦ'`; in every degree it is
  `β` (after Mathlib's identification `mapHomologicalComplexCompIso`, an
  identity).
- `standardTotalSystemMapOfHom N P ε f`: for a morphism `f : K ⟶ K'` of
  `ℓ`-divisible systems of `ℕ`-graded complexes, the induced morphism
  `K.standardTotalSystem N P ε ⟶ K'.standardTotalSystem N P ε` of total
  complexes (rows `q < N`) of the standard resolutions along `P`
  (`totalSystemMap` of the standard resolution applied to `f`).
- `standardTotalSystemMapOfHom_comp_toExtend N P ε f hK hK'`: for `K` and
  `K'` vanishing in degrees `q ≥ N`, the Library's
  `standardTotalSystemToExtend` (totalized augmentation followed by the
  comparison with the system extended to `ℤ`) is natural:
  `standardTotalSystemMapOfHom N P ε f ≫ K'.standardTotalSystemToExtend =
  K.standardTotalSystemToExtend ≫` (the extension of `f` to `ℤ`). Proof, at
  each level and degree: naturality of the augmentation of the standard
  resolution, mapped by the total complex functor, and
  `columnComparisonF_naturality`.

## The transition morphism

`G` is a topological group, `K` an `ℓ`-divisible system of `ℕ`-graded
complexes of smooth representations of `G`, `H' ≤ H` normal subgroups.

- `quotientInvariantsComplexesChange K hHH' hK hK'`: the morphism of
  `ℓ`-divisible systems `Res_π K^H ⟶ K^{H'}` (with `Res_π` applied
  degreewise), the inclusion of invariants in every degree of every level
  (`mapComplexesCompHom` of `smoothQuotientInvariantsChange`).
- `quotientInvariantsComplexesChange_comp_inclusion K hHH' hK hK'`: after
  inflation to `G`, this inclusion followed by the inclusion of the inflated
  `H'`-invariants into the underlying complexes of representations
  (`quotientInvariantsComplexesInclusion` for `H'`, after
  `inflateQuotientInvariantsComplexesHom`) is the inclusion of the inflated
  `H`-invariants. The two sides agree elementwise (`ext x; rfl`).

Now `H` and `H'` have finite index, `G ⧸ H'` is a `Fintype` and `G ⧸ H` has
decidable equality (needed by `groupStandardTotalSystemMap`), `N : ℕ`, and
`hk` says that `|ker π|` (`Nat.card`) is a unit in `R`. Mathematically
`ker π` is the image of `H` in `G ⧸ H'`, of order `[H : H']`; this
identification is not used.

- `quotientInvariantsTransition K hHH' N hK hK' hk`: the morphism of
  `ℓ`-divisible systems of `ℤ`-graded complexes of representations of `G`
  from `inflatedQuotientInvariantsTotalSystem N K H hK` (`Inf_H C^{•,H}`) to
  `inflatedQuotientInvariantsTotalSystem N K H' hK'` (`Inf_{H'} C^{•,H'}`).
  It is the composite of
  1. `mapCompHom` of `quotientInflationResIso` (identity components),
     rewriting `Inf_H C^{•,H}` as `Inf_{H'} Res_π C^{•,H}`;
  2. `Inf_{H'}` applied to the composite of
     - `groupStandardTotalSystemMap π hπ hk N K^H : Res_π C^{•,H} ⟶` the
       total complexes of the standard resolutions along
       `Ind_1^{G⧸H'} Res_1^{G⧸H'}` of `Res_π K^H`: in resolution degree `r`
       the iterated normalized fiber sum
       `⟦γ ⊗ v⟧ ↦ |ker π|⁻¹ ∑_{π γ' = γ} ⟦γ' ⊗ v⟧` of the StandardMap
       module; and
     - `standardTotalSystemMapOfHom` of
       `quotientInvariantsComplexesChange`: the map of these total
       complexes induced by the inclusion `Res_π K^H ⟶ K^{H'}`, landing in
       `C^{•,H'}`.
- `quotientInvariantsTransition_comp_toRepExtend K hHH' N hK hK' hk hN`: for
  `K` vanishing in degrees `q ≥ N` (`hN`), the transition morphism followed
  by `quotientInvariantsTotalSystemToRepExtend N K H' hK' hN` (the
  comparison of the InvariantComparison module from `Inf_{H'} C^{•,H'}` to
  the underlying complexes of representations of `K` extended to `ℤ`) is
  `quotientInvariantsTotalSystemToRepExtend N K H hK hN`. Proof, at each
  level: `extendComparison_comp_eq` with `F₁ = Res_π`, `F₂ = Inf_{H'}`,
  `F₃ = Inf_H`, `α = quotientInflationResIso`. Its hypothesis `h₁` is
  `groupStandardTotalSystemMap_tower_app_comp` (the fiber sum is compatible
  with the comparisons to the extended systems), `h₂` is
  `standardTotalSystemMapOfHom_comp_toExtend` for
  `quotientInvariantsComplexesChange`, and `h₃` is
  `quotientInvariantsComplexesChange_comp_inclusion`.
- `quasiIso_quotientInvariantsTransition_tower_app K hHH' N hS hH hH' hR hK
  hK' hk hN m htriv`: given `ProPInvariantSubcomplexStatement` (`hS`), for
  `H` and `H'` pro-`p` (`IsProPSubgroup p`), `p` a unit in `R` (`hR`), and a
  level `m` at which `H` acts trivially on the cohomology of
  `K.toRepComplexes.obj m` (`htriv`), the level `m` of the transition
  morphism is a quasi-isomorphism. Proof: `htriv` for `H` gives it for
  `H' ≤ H`; by `quasiIso_quotientInvariantsTotalSystemToRepExtend` both
  comparisons are quasi-isomorphisms at level `m`, and by the previous
  theorem the comparison for `H` is the transition followed by the
  comparison for `H'`; Mathlib's `quasiIso_iff_comp_right` concludes.

## Provenance and interpretation

Harris, *Galois properties of cohomological automorphic forms on GL(n)*,
J. Math. Kyoto Univ. 39-2 (1999), section 2, printed pp.305–306. On p.305
he resolves `M_m^{q,H} = G_m^q(U(ẽ)_F̄)^H` by iterating (2.4)
`Z_ℓ[S(ẽ)/H] ⊗_{Z_ℓ} (•) → •`, and on p.306, after forming `C_m^{•,H}`:
"When we replace H by a subgroup H' which is normal in S(e), we obtain a
natural isomorphism C_m^{•,H} = [C_m^{•,H'}]^H." He then takes the direct
limit as `H` shrinks to the identity to obtain (2.6). Worker 61 read these
passages in the scanned original (p.306 prints `S(e)` where p.305 has
`S(ẽ)`).

1. The isomorphism `C_m^{•,H} = [C_m^{•,H'}]^H` is not formalized, and we
   do not claim it. The following computation is ours, not Harris's. Let
   `S(ẽ)` act on `Z/ℓ^m[S(ẽ)/H'] ⊗ X` through the group ring factor; this
   is the free module structure Harris requires, and the diagonal action
   gives an isomorphic module. Then the `H`-invariants of
   `Z/ℓ^m[S(ẽ)/H'] ⊗ X` are the elements whose coefficients are constant on
   the cosets of `H/H'`. As a module they are isomorphic to
   `Z/ℓ^m[S(ẽ)/H] ⊗ X`. The top total degree of `C_m^{•,H'}` has the single
   summand `(q, 0)` for the top row `q`. So in that degree
   `[C_m^{•,H'}]^H` is isomorphic to `Z/ℓ^m[S(ẽ)/H] ⊗ M_m^{q,H'}`, while
   `C_m^{•,H}` is `Z/ℓ^m[S(ẽ)/H] ⊗ M_m^{q,H}`. Thus the two complexes are
   built from `M_m^{q,H'}` and `M_m^{q,H}` respectively, and the
   identification cannot be the evident one. When these modules are finite
   and `M_m^{q,H} ≠ M_m^{q,H'}`, the two terms have different orders, and
   no isomorphism of complexes exists. This holds at least for the standard
   resolution as we read (2.4). We read Harris's sentence as asserting the
   compatibility between the constructions for `H` and `H'` that the direct
   limit needs.
2. What is formalized instead. A transition morphism from `C_m^{•,H}` to
   `C_m^{•,H'}`, both inflated to `S(ẽ)` (here `G`), that is compatible with
   the comparisons to the underlying complexes. It is also a
   quasi-isomorphism wherever the comparisons are. Its construction is ours:
   the normalized fiber sum along `S(ẽ)/H' → S(ẽ)/H`, then the inclusion
   `M_m^{q,H} ⊆ M_m^{q,H'}`. It needs `|H/H'|` to be invertible in the
   coefficients. Without the normalization the fiber sum is not compatible
   with the augmentations (StandardMap module). In Harris's setting `H` is
   pro-`p`. If `H'` is open in `H` (Harris says only that `H'` is normal in
   `S(e)`), then `[H : H']` is a power of `p`, invertible in `Z/ℓ^mZ` since
   `p ≠ ℓ`. This is not formalized: `hk` is an explicit hypothesis.
3. Hypotheses. As in the InvariantComparison module, the quasi-isomorphism
   depends on Worker 3's unproved `ProPInvariantSubcomplexStatement`
   (`hS`). Also as there, the trivial action `htriv` is a hypothesis at the
   single level `m`, on the cohomology of the abstract complex of
   representations `K.toRepComplexes.obj m`. Harris's trivial action is on
   the compactly supported cohomology `H_c^q(U(ẽ)_F̄, ℤ/ℓ^mℤ)`, identified
   with the cohomology of `G_m^•(U(ẽ)_F̄)` only through his (2.3), which is
   not formalized. Harris's `H` is open; openness is not used. Finite index
   of `H` and `H'`, `hK`, `hK'`, `hk` and `hN` are explicit hypotheses.

## Scope

The module constructs the transition morphism for one pair `H' ≤ H` and
proves its compatibility with the comparisons and the level-wise
quasi-isomorphism under the hypotheses above. It does not prove
transitivity of the transition morphisms for `H'' ≤ H' ≤ H`, take the
direct limit over `H`, or construct (2.6), (2.7) or Lemma 2.8. Nor does it
prove any freeness or projectivity.

Source registration: Harris 1999,
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.

Dependencies are the modules named above, pinned to Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
