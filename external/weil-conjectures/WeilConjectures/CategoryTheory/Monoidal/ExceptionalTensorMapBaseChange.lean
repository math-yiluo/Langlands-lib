/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.ProjectionBaseChange

/-!

# The tensor map of an exceptional inverse image under base change

The data model the derived categories `𝒵 = D(X)`, `𝒴 = D(Y)`, `𝒱 = D(X')`, `𝒲 = D(Y')` of a
cartesian square of schemes, the base change of `f : X ⟶ Y` along `Y' ⟶ Y`:
```
𝒵 ──qZ──▶ 𝒱
│g        │G
▼         ▼
𝒴 ──q───▶ 𝒲
```
as in `WeilConjectures.CategoryTheory.Monoidal.ProjectionBaseChange`: `g : 𝒵 ⥤ 𝒴` and
`G : 𝒱 ⥤ 𝒲` play the compactly supported direct images `Rf_!` and `Rf'_!`, with right adjoints
`gu`, `Gu` (the exceptional inverse images `Rf^!`, `Rf'^!`), `gs` and `Gs` play the inverse images
`Lf^*` and `Lf'^*`, with projection morphisms `pfg`, `pfG`, the monoidal functors `q : 𝒴 ⥤ 𝒲` and
`qZ : 𝒵 ⥤ 𝒱` play `Lg^*` and `Lg'^*`, and `BC : g ⋙ q ⟶ qZ ⋙ G` is compact-support base change.

The *tensor map* `γ_K : gs K ⊗ gu 𝟙 ⟶ gu K` is the adjoint of the symmetry, the inverse projection
morphism and the counit at the unit; the *exceptional base change* `b_K : qZ (gu K) ⟶ Gu (q K)` is
the adjoint of the inverse base change followed by the pulled-back counit. The main statement
`CategoryTheory.ProjectionBaseChange.map_tensorMap_comp_baseChange` (blueprint
`proposition-exceptional-inverse-image-smooth-morphism`, compatibility of (G11) with (G12);
`proposition-compatibility-purity-base-change`, tensor map) says that `qZ γ_K ≫ b_K` is the tensor
map of `G` at `q K` precomposed with the base change at the unit: if the projection morphisms are
compatible with base change (`PFBaseChange`), then
```
qZ (gs K ⊗ gu 𝟙) ──qZ γ_K──▶ qZ (gu K) ──b_K──▶ Gu (q K)
      │≅                                          ▲
      ▼                                           │ γ'_{q K}
Gs (q K) ⊗ qZ (gu 𝟙) ──1 ⊗ b_𝟙──▶ Gs (q K) ⊗ Gu (q 𝟙) ≅ Gs (q K) ⊗ Gu 𝟙
```
commutes. The morphisms `γ`, `γ'`, `b` are taken as variables characterised by their adjoints, so
that the statement applies to any construction of them.

-/

@[expose] public section

open CategoryTheory MonoidalCategory Functor.OplaxMonoidal

namespace CategoryTheory.ProjectionBaseChange

variable {𝒱 𝒲 𝒴 𝒵 : Type*} [Category 𝒱] [Category 𝒲] [Category 𝒴] [Category 𝒵]
  [MonoidalCategory 𝒱] [MonoidalCategory 𝒲] [MonoidalCategory 𝒴] [MonoidalCategory 𝒵]
  [BraidedCategory 𝒱] [BraidedCategory 𝒵]
  {G : 𝒱 ⥤ 𝒲} {Gu : 𝒲 ⥤ 𝒱} {Gs : 𝒲 ⥤ 𝒱} (aG : G ⊣ Gu)
  {g : 𝒵 ⥤ 𝒴} {gu : 𝒴 ⥤ 𝒵} {gs : 𝒴 ⥤ 𝒵} (ag : g ⊣ gu)
  (q : 𝒴 ⥤ 𝒲) [q.Monoidal] (qZ : 𝒵 ⥤ 𝒱) [qZ.Monoidal]
  (BC : g ⋙ q ⟶ qZ ⋙ G) [IsIso BC] (θ : q ⋙ Gs ≅ gs ⋙ qZ)
  (pfg : curriedTensorInsertFunctor₁ g ⟶
    curriedTensorPost g ⋙ (Functor.whiskeringLeft 𝒴 𝒵 𝒴).obj gs)
  (pfG : curriedTensorInsertFunctor₁ G ⟶
    curriedTensorPost G ⋙ (Functor.whiskeringLeft 𝒲 𝒱 𝒲).obj Gs)
  [∀ A B, IsIso ((pfg.app A).app B)] [∀ A B, IsIso ((pfG.app A).app B)]

/-- **The tensor map is compatible with base change.** Let `γ_K : gs K ⊗ gu 𝟙 ⟶ gu K` and
`γ'_{q K} : Gs (q K) ⊗ Gu 𝟙 ⟶ Gu (q K)` be the tensor maps (characterised by their adjoints `hγ`,
`hγ'`) and `b_K : qZ (gu K) ⟶ Gu (q K)`, `b_𝟙 : qZ (gu 𝟙) ⟶ Gu (q 𝟙)` the exceptional base change
maps (characterised by `hb`, `hb₁`). If the projection morphisms are compatible with base change
(`hPF`) and `qZ` is braided (`hbr`), then `qZ γ_K ≫ b_K` is `γ'_{q K}` precomposed with the
tensor structure of `qZ`, `θ` and `1 ⊗ b_𝟙` (followed by the unit isomorphism of `q`). -/
theorem map_tensorMap_comp_baseChange
    (hPF : PFBaseChange q qZ BC θ pfg pfG)
    (hbr : ∀ A B : 𝒵, qZ.map (β_ A B).hom ≫ δ qZ B A = δ qZ A B ≫ (β_ (qZ.obj A) (qZ.obj B)).hom)
    (K : 𝒴) (γ : gs.obj K ⊗ gu.obj (𝟙_ 𝒴) ⟶ gu.obj K)
    (hγ : (ag.homEquiv _ _).symm γ = g.map (β_ (gs.obj K) (gu.obj (𝟙_ 𝒴))).hom ≫
      inv ((pfg.app (gu.obj (𝟙_ 𝒴))).app K) ≫ (ag.counit.app (𝟙_ 𝒴) ▷ K) ≫ (λ_ K).hom)
    (γ' : Gs.obj (q.obj K) ⊗ Gu.obj (𝟙_ 𝒲) ⟶ Gu.obj (q.obj K))
    (hγ' : (aG.homEquiv _ _).symm γ' = G.map (β_ (Gs.obj (q.obj K)) (Gu.obj (𝟙_ 𝒲))).hom ≫
      inv ((pfG.app (Gu.obj (𝟙_ 𝒲))).app (q.obj K)) ≫ (aG.counit.app (𝟙_ 𝒲) ▷ q.obj K) ≫
        (λ_ (q.obj K)).hom)
    (b : qZ.obj (gu.obj K) ⟶ Gu.obj (q.obj K))
    (hb : (aG.homEquiv _ _).symm b = inv (BC.app (gu.obj K)) ≫ q.map (ag.counit.app K))
    (b₁ : qZ.obj (gu.obj (𝟙_ 𝒴)) ⟶ Gu.obj (q.obj (𝟙_ 𝒴)))
    (hb₁ : (aG.homEquiv _ _).symm b₁ =
      inv (BC.app (gu.obj (𝟙_ 𝒴))) ≫ q.map (ag.counit.app (𝟙_ 𝒴))) :
    qZ.map γ ≫ b = δ qZ (gs.obj K) (gu.obj (𝟙_ 𝒴)) ≫
      (θ.inv.app K ▷ qZ.obj (gu.obj (𝟙_ 𝒴))) ≫
      (Gs.obj (q.obj K) ◁ (b₁ ≫ Gu.map (η q))) ≫ γ' := by
  apply (aG.homEquiv _ _).symm.injective
  -- the adjoint of the left side
  have hL : (aG.homEquiv _ _).symm (qZ.map γ ≫ b) =
      inv (BC.app (gs.obj K ⊗ gu.obj (𝟙_ 𝒴))) ≫ q.map ((ag.homEquiv _ _).symm γ) := by
    rw [Adjunction.homEquiv_naturality_left_symm, hb, Adjunction.homEquiv_counit, q.map_comp,
      ← Category.assoc, ← Category.assoc]
    congr 1
    rw [IsIso.eq_inv_comp, ← Category.assoc, IsIso.comp_inv_eq]
    exact (BC.naturality γ).symm
  -- the adjoint of the right side
  have hR : (aG.homEquiv _ _).symm (δ qZ (gs.obj K) (gu.obj (𝟙_ 𝒴)) ≫
      (θ.inv.app K ▷ qZ.obj (gu.obj (𝟙_ 𝒴))) ≫
      (Gs.obj (q.obj K) ◁ (b₁ ≫ Gu.map (η q))) ≫ γ') =
      G.map (δ qZ (gs.obj K) (gu.obj (𝟙_ 𝒴))) ≫ G.map (θ.inv.app K ▷ qZ.obj (gu.obj (𝟙_ 𝒴))) ≫
        G.map (β_ (Gs.obj (q.obj K)) (qZ.obj (gu.obj (𝟙_ 𝒴)))).hom ≫
        inv ((pfG.app (qZ.obj (gu.obj (𝟙_ 𝒴)))).app (q.obj K)) ≫
        ((inv (BC.app (gu.obj (𝟙_ 𝒴))) ≫ q.map (ag.counit.app (𝟙_ 𝒴)) ≫ η q) ▷ q.obj K) ≫
        (λ_ (q.obj K)).hom := by
    simp only [Adjunction.homEquiv_naturality_left_symm, hγ']
    have h₁ := BraidedCategory.braiding_naturality_right (Gs.obj (q.obj K)) (b₁ ≫ Gu.map (η q))
    have h₂ : G.map ((b₁ ≫ Gu.map (η q)) ▷ Gs.obj (q.obj K)) ≫
        inv ((pfG.app (Gu.obj (𝟙_ 𝒲))).app (q.obj K)) =
        inv ((pfG.app (qZ.obj (gu.obj (𝟙_ 𝒴)))).app (q.obj K)) ≫
          (G.map (b₁ ≫ Gu.map (η q)) ▷ q.obj K) := by
      rw [IsIso.eq_inv_comp, ← Category.assoc, IsIso.comp_inv_eq]
      exact (congr_app (pfG.naturality (b₁ ≫ Gu.map (η q))) (q.obj K)).symm
    have h₃ : G.map (b₁ ≫ Gu.map (η q)) ≫ aG.counit.app (𝟙_ 𝒲) =
        inv (BC.app (gu.obj (𝟙_ 𝒴))) ≫ q.map (ag.counit.app (𝟙_ 𝒴)) ≫ η q := by
      rw [G.map_comp, Category.assoc]
      erw [aG.counit_naturality]
      rw [← Category.assoc,
        ← Adjunction.homEquiv_counit, hb₁, Category.assoc]
    rw [← G.map_comp_assoc (Gs.obj (q.obj K) ◁ (b₁ ≫ Gu.map (η q))), h₁, G.map_comp_assoc,
      reassoc_of% h₂, ← comp_whiskerRight_assoc, h₃]
  rw [hL, hR, hγ]
  -- the projection formula compatibility, inverted
  have hP : inv (BC.app (gu.obj (𝟙_ 𝒴) ⊗ gs.obj K)) ≫
      q.map (inv ((pfg.app (gu.obj (𝟙_ 𝒴))).app K)) =
      G.map (δ qZ (gu.obj (𝟙_ 𝒴)) (gs.obj K)) ≫ G.map (qZ.obj (gu.obj (𝟙_ 𝒴)) ◁ θ.inv.app K) ≫
        inv ((pfG.app (qZ.obj (gu.obj (𝟙_ 𝒴)))).app (q.obj K)) ≫
        (inv (BC.app (gu.obj (𝟙_ 𝒴))) ▷ q.obj K) ≫ inv (δ q (g.obj (gu.obj (𝟙_ 𝒴))) K) := by
    have h := hPF (gu.obj (𝟙_ 𝒴)) K
    rw [IsIso.inv_comp_eq, Functor.map_inv]
    apply IsIso.inv_eq_of_hom_inv_id
    rw [reassoc_of% h]
    simp [← comp_whiskerRight_assoc]
  -- moving the symmetry past the inverse base change
  have h₄ : inv (BC.app (gs.obj K ⊗ gu.obj (𝟙_ 𝒴))) ≫
      q.map (g.map (β_ (gs.obj K) (gu.obj (𝟙_ 𝒴))).hom) =
      G.map (qZ.map (β_ (gs.obj K) (gu.obj (𝟙_ 𝒴))).hom) ≫
        inv (BC.app (gu.obj (𝟙_ 𝒴) ⊗ gs.obj K)) := by
    rw [IsIso.eq_comp_inv, Category.assoc, IsIso.inv_comp_eq]
    have := BC.naturality (β_ (gs.obj K) (gu.obj (𝟙_ 𝒴))).hom
    dsimp at this
    exact this
  -- the tensor structure of `q` and the counit
  have h₅ : inv (δ q (g.obj (gu.obj (𝟙_ 𝒴))) K) ≫ q.map (ag.counit.app (𝟙_ 𝒴) ▷ K) ≫
      q.map (λ_ K).hom =
      (q.map (ag.counit.app (𝟙_ 𝒴)) ▷ q.obj K) ≫ (η q ▷ q.obj K) ≫ (λ_ (q.obj K)).hom := by
    rw [IsIso.inv_comp_eq, reassoc_of% (δ_natural_left q (ag.counit.app (𝟙_ 𝒴)) K),
      ← Functor.OplaxMonoidal.left_unitality_hom]
  -- the braiding
  have h₆ : G.map (qZ.map (β_ (gs.obj K) (gu.obj (𝟙_ 𝒴))).hom) ≫
      G.map (δ qZ (gu.obj (𝟙_ 𝒴)) (gs.obj K)) ≫
      G.map (qZ.obj (gu.obj (𝟙_ 𝒴)) ◁ θ.inv.app K) =
      G.map (δ qZ (gs.obj K) (gu.obj (𝟙_ 𝒴))) ≫ G.map (θ.inv.app K ▷ qZ.obj (gu.obj (𝟙_ 𝒴))) ≫
        G.map (β_ (Gs.obj (q.obj K)) (qZ.obj (gu.obj (𝟙_ 𝒴)))).hom := by
    simp only [← G.map_comp]
    congr 1
    rw [reassoc_of% (hbr (gs.obj K) (gu.obj (𝟙_ 𝒴)))]
    exact congrArg (δ qZ (gs.obj K) (gu.obj (𝟙_ 𝒴)) ≫ ·)
      (BraidedCategory.braiding_naturality_left (θ.inv.app K) _).symm
  simp only [q.map_comp]
  rw [reassoc_of% h₄, reassoc_of% hP, h₅, ← reassoc_of% h₆]
  simp only [comp_whiskerRight, Category.assoc]

end CategoryTheory.ProjectionBaseChange
