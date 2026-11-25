/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Functor.Derived.Adjunction
public import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# Complements on derived adjunctions

If `α : L₁ ⋙ G' ⟶ G ⋙ L₂` factors as `L₁ ⋙ G' ≅ L₁ ⋙ G'' ⟶ G ⋙ L₂` through an
isomorphism `e : G' ≅ G''`, the derived adjunction `G' ⊣ F'` built from `α` is the derived
adjunction `G'' ⊣ F'` built from the second factor, transported along `e`.

Let `adj₁ : G₁ ⊣ F₁` and `adj₂ : G₂ ⊣ F₂` be adjunctions, `σ : H₁ ⋙ G₂ ⟶ G₁ ⋙ H₂` a square of
functors and `θ : H₁' ⋙ G₂' ⟶ G₁' ⋙ H₂'` a square of functors between localized categories
which is computed by `σ` (modulo given natural transformations `γᵢ : Lᵢ ⋙ Hᵢ' ⟶ Hᵢ ⋙ L'ᵢ`
comparing `Hᵢ'` with `Hᵢ`). Then the mate of `θ` with respect to the derived adjunctions
`Adjunction.derived` is computed by the mate of `σ`, through the units `β` of the derived right
adjoints (`CategoryTheory.Adjunction.derived_mateEquiv_app_fac`).
-/

@[expose] public section

namespace CategoryTheory

variable {C₁ C₂ D₁ D₂ : Type*} [Category* C₁] [Category* C₂] [Category* D₁] [Category* D₂]
  {G : C₁ ⥤ C₂} {F : C₂ ⥤ C₁} (adj : G ⊣ F)
  {L₁ : C₁ ⥤ D₁} {L₂ : C₂ ⥤ D₂} (W₁ : MorphismProperty C₁) (W₂ : MorphismProperty C₂)
  [L₁.IsLocalization W₁] [L₂.IsLocalization W₂]
  {G' G'' : D₁ ⥤ D₂} {F' : D₂ ⥤ D₁}
  (α : L₁ ⋙ G' ⟶ G ⋙ L₂) (α' : L₁ ⋙ G'' ⟶ G ⋙ L₂) (β : F ⋙ L₁ ⟶ L₂ ⋙ F')

namespace Adjunction

open CategoryTheory.Functor

lemma derived_eq_ofNatIsoLeft (e : G' ≅ G'') (hα : α = whiskerLeft L₁ e.hom ≫ α')
    [G'.IsLeftDerivedFunctor α W₁] [G''.IsLeftDerivedFunctor α' W₁]
    [F'.IsRightDerivedFunctor β W₂]
    [(G' ⋙ F').IsLeftDerivedFunctor ((Functor.associator _ _ _).inv ≫ whiskerRight α F') W₁]
    [(F' ⋙ G').IsRightDerivedFunctor (whiskerRight β G' ≫ (Functor.associator _ _ _).hom) W₂]
    [(G'' ⋙ F').IsLeftDerivedFunctor ((Functor.associator _ _ _).inv ≫ whiskerRight α' F') W₁]
    [(F' ⋙ G'').IsRightDerivedFunctor
      (whiskerRight β G'' ≫ (Functor.associator _ _ _).hom) W₂] :
    adj.derived W₁ W₂ α β = (adj.derived W₁ W₂ α' β).ofNatIsoLeft e.symm := by
  apply Adjunction.ext_counit
  apply (F' ⋙ G').rightDerived_ext (whiskerRight β G' ≫ (Functor.associator _ _ _).hom) W₂
  ext X
  subst hα
  have h₁ := adj.derivedε_fac_app W₂ (whiskerLeft L₁ e.hom ≫ α') β X
  have h₂ := adj.derivedε_fac_app W₂ α' β X
  have h₃ := e.hom.naturality (β.app X)
  dsimp at h₁ h₂ h₃ ⊢
  simp only [derived_counit, ofNatIsoLeft_counit, Iso.symm_inv, NatTrans.comp_app,
    whiskerLeft_app, Category.comp_id]
  rw [h₁, reassoc_of% h₃, h₂, Category.assoc]

end Adjunction

end CategoryTheory


open CategoryTheory.Functor

namespace CategoryTheory

variable {C₁ C₂ C₃ C₄ D₁ D₂ D₃ D₄ : Type*} [Category* C₁] [Category* C₂] [Category* C₃]
  [Category* C₄] [Category* D₁] [Category* D₂] [Category* D₃] [Category* D₄]
  {G₁ : C₁ ⥤ C₂} {F₁ : C₂ ⥤ C₁} (adj₁ : G₁ ⊣ F₁) {G₂ : C₃ ⥤ C₄} {F₂ : C₄ ⥤ C₃} (adj₂ : G₂ ⊣ F₂)
  {H₁ : C₁ ⥤ C₃} {H₂ : C₂ ⥤ C₄}
  {L₁ : C₁ ⥤ D₁} {L₂ : C₂ ⥤ D₂} {L₃ : C₃ ⥤ D₃} {L₄ : C₄ ⥤ D₄}
  (W₁ : MorphismProperty C₁) (W₂ : MorphismProperty C₂) (W₃ : MorphismProperty C₃)
  (W₄ : MorphismProperty C₄)
  [L₁.IsLocalization W₁] [L₂.IsLocalization W₂] [L₃.IsLocalization W₃] [L₄.IsLocalization W₄]
  {G₁' : D₁ ⥤ D₂} {F₁' : D₂ ⥤ D₁} {G₂' : D₃ ⥤ D₄} {F₂' : D₄ ⥤ D₃}
  {H₁' : D₁ ⥤ D₃} {H₂' : D₂ ⥤ D₄}
  (α₁ : L₁ ⋙ G₁' ⟶ G₁ ⋙ L₂) (β₁ : F₁ ⋙ L₁ ⟶ L₂ ⋙ F₁')
  (α₂ : L₃ ⋙ G₂' ⟶ G₂ ⋙ L₄) (β₂ : F₂ ⋙ L₃ ⟶ L₄ ⋙ F₂')
  (γ₁ : L₁ ⋙ H₁' ⟶ H₁ ⋙ L₃) (γ₂ : L₂ ⋙ H₂' ⟶ H₂ ⋙ L₄)
  [G₁'.IsLeftDerivedFunctor α₁ W₁] [F₁'.IsRightDerivedFunctor β₁ W₂]
  [(G₁' ⋙ F₁').IsLeftDerivedFunctor ((Functor.associator _ _ _).inv ≫ whiskerRight α₁ F₁') W₁]
  [(F₁' ⋙ G₁').IsRightDerivedFunctor (whiskerRight β₁ G₁' ≫ (Functor.associator _ _ _).hom) W₂]
  [G₂'.IsLeftDerivedFunctor α₂ W₃] [F₂'.IsRightDerivedFunctor β₂ W₄]
  [(G₂' ⋙ F₂').IsLeftDerivedFunctor ((Functor.associator _ _ _).inv ≫ whiskerRight α₂ F₂') W₃]
  [(F₂' ⋙ G₂').IsRightDerivedFunctor (whiskerRight β₂ G₂' ≫ (Functor.associator _ _ _).hom) W₄]

namespace Adjunction

/-- **The derived mate is computed by the underived mate.** Let `θ : H₁' ⋙ G₂' ⟶ G₁' ⋙ H₂'` be a
square between the derived functors which, on the object `L₁ (F₁ K)`, is computed by a square
`σ : H₁ ⋙ G₂ ⟶ G₁ ⋙ H₂` of underived functors through the comparison maps `αᵢ` of the derived
left adjoints and `γᵢ` of the functors `Hᵢ'` (hypothesis `hθ`). Then the mate of `θ` with respect
to the derived adjunctions `adj₁.derived` and `adj₂.derived`, at `L₂ K` and read through the
comparison maps `β₁` and `γ₂`, is the mate of `σ` followed by the comparison map `β₂`:
```
H₁' (L₁ (F₁ K)) ──H₁'.map (β₁.app K)──▶ H₁' (F₁' (L₂ K)) ──(mate of θ)──▶ F₂' (H₂' (L₂ K))
      │                                                                 │
γ₁.app (F₁ K)                                                F₂'.map (γ₂.app K)
      ▼                                                                 ▼
L₃ (H₁ (F₁ K)) ──L₃.map ((mate of σ).app K)──▶ L₃ (F₂ (H₂ K)) ──β₂.app (H₂ K)──▶ F₂' (L₄ (H₂ K))
```
-/
theorem derived_mateEquiv_app_fac (σ : TwoSquare H₁ G₁ G₂ H₂) (θ : TwoSquare H₁' G₁' G₂' H₂')
    (K : C₂)
    (hθ : θ.app (L₁.obj (F₁.obj K)) ≫ H₂'.map (α₁.app (F₁.obj K)) ≫
        γ₂.app (G₁.obj (F₁.obj K)) =
      G₂'.map (γ₁.app (F₁.obj K)) ≫ α₂.app (H₁.obj (F₁.obj K)) ≫
        L₄.map (σ.app (F₁.obj K))) :
    H₁'.map (β₁.app K) ≫ (mateEquiv (adj₁.derived W₁ W₂ α₁ β₁) (adj₂.derived W₃ W₄ α₂ β₂)
        θ).app (L₂.obj K) ≫ F₂'.map (γ₂.app K) =
      γ₁.app (F₁.obj K) ≫ L₃.map ((mateEquiv adj₁ adj₂ σ).app K) ≫
        β₂.app (H₂.obj K) := by
  have hmate (Z : D₂) : (mateEquiv (adj₁.derived W₁ W₂ α₁ β₁) (adj₂.derived W₃ W₄ α₂ β₂)
      θ).app Z = (adj₂.derived W₃ W₄ α₂ β₂).unit.app (H₁'.obj (F₁'.obj Z)) ≫
        F₂'.map (θ.app (F₁'.obj Z)) ≫
        F₂'.map (H₂'.map ((adj₁.derived W₁ W₂ α₁ β₁).counit.app Z)) := by
    simp [mateEquiv_apply]
  have hmate' : (mateEquiv adj₁ adj₂ σ).app K =
      adj₂.unit.app (H₁.obj (F₁.obj K)) ≫ F₂.map (σ.app (F₁.obj K)) ≫
        F₂.map (H₂.map (adj₁.counit.app K)) := by
    simp [mateEquiv_apply]
  have h₁ := (adj₂.derived W₃ W₄ α₂ β₂).unit.naturality (H₁'.map (β₁.app K))
  have h₂ := θ.naturality (β₁.app K)
  have h₃ := adj₁.derivedε_fac_app W₂ α₁ β₁ K
  have h₄ := γ₂.naturality (adj₁.counit.app K)
  have h₅ := (adj₂.derived W₃ W₄ α₂ β₂).unit.naturality (γ₁.app (F₁.obj K))
  have h₆ := adj₂.derivedη_fac_app W₃ α₂ β₂ (H₁.obj (F₁.obj K))
  have h₇ := β₂.naturality (σ.app (F₁.obj K) ≫ H₂.map (adj₁.counit.app K))
  simp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj, Functor.id_map] at h₁ h₂ h₄ h₅ h₇
  simp only [derived_unit, derived_counit] at hmate h₁ h₅ ⊢
  rw [hmate]
  simp only [Category.assoc]
  rw [reassoc_of% h₁]
  simp only [← Functor.map_comp]
  rw [reassoc_of% h₂, ← Functor.map_comp_assoc H₂', h₃, Functor.map_comp_assoc, h₄,
    reassoc_of% hθ]
  simp only [Functor.map_comp]
  rw [← reassoc_of% h₅, reassoc_of% h₆, hmate']
  simp only [Functor.map_comp, Category.assoc] at h₇ ⊢
  rw [← h₇]

end Adjunction

end CategoryTheory
