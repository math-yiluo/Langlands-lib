/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Sites.PushforwardMonoidal

/-!
# Whiskering pushforwards of sheaves by a natural transformation is monoidal

For continuous functors `F F' : C ⥤ D` and a natural transformation `τ : F ⟶ F'`, the induced
natural transformation `F'_* ⟶ F_*` of pushforwards of sheaves
(`CategoryTheory.Functor.sheafPushforwardContinuousNatTrans`, restriction along `τ`) is
monoidal for the lax monoidal structures of the pushforwards
(`CategoryTheory.Functor.isMonoidal_sheafPushforwardContinuousNatTrans`). As for
`CategoryTheory.Functor.isMonoidal_sheafPushforwardContinuousComp'_hom`, this is checked on
underlying presheaves, where both lax structures are restrictions of the one of
`sheafToPresheaf`.
-/

@[expose] public section

namespace CategoryTheory.Functor

open MonoidalCategory LaxMonoidal

attribute [local instance] Sheaf.monoidalCategory

variable {C : Type*} [Category C] {D : Type*} [Category D] {F F' : C ⥤ D} (τ : F ⟶ F')
  (A : Type*) [Category A] [MonoidalCategory A] [BraidedCategory A]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [(J.W (A := A)).IsMonoidal] [HasWeakSheafify J A]
  [(K.W (A := A)).IsMonoidal] [HasWeakSheafify K A] [F.IsContinuous J K] [F'.IsContinuous J K]

lemma ε_comp_sheafPushforwardContinuousNatTrans_app :
    ε (F'.sheafPushforwardContinuous A J K) ≫
        (sheafPushforwardContinuousNatTrans τ A J K).app (𝟙_ _) =
      ε (F.sheafPushforwardContinuous A J K) := by
  apply Sheaf.hom_ext_of_ε_comp
  ext U
  simp only [Functor.map_comp, NatTrans.comp_app]
  erw [ε_sheafToPresheaf_app_comp_ε_sheafPushforwardContinuous_app_assoc,
    ε_sheafToPresheaf_app_comp_ε_sheafPushforwardContinuous_app]
  simpa using ((ε (sheafToPresheaf K A)).naturality (τ.app U.unop).op).symm

lemma μ_comp_sheafPushforwardContinuousNatTrans_app (X Y : Sheaf K A) :
    μ (F'.sheafPushforwardContinuous A J K) X Y ≫
        (sheafPushforwardContinuousNatTrans τ A J K).app (X ⊗ Y) =
      ((sheafPushforwardContinuousNatTrans τ A J K).app X ⊗ₘ
          (sheafPushforwardContinuousNatTrans τ A J K).app Y) ≫
        μ (F.sheafPushforwardContinuous A J K) X Y := by
  apply Sheaf.hom_ext_of_μ_comp
  ext U
  have h := congr_app (μ_natural (sheafToPresheaf J A)
    ((sheafPushforwardContinuousNatTrans τ A J K).app X)
    ((sheafPushforwardContinuousNatTrans τ A J K).app Y)) U
  simp only [NatTrans.comp_app] at h
  simp only [Functor.map_comp, NatTrans.comp_app]
  erw [μ_sheafToPresheaf_app_comp_μ_sheafPushforwardContinuous_app_assoc, ← reassoc_of% h,
    μ_sheafToPresheaf_app_comp_μ_sheafPushforwardContinuous_app]
  simpa using ((μ (sheafToPresheaf K A) X Y).naturality (τ.app U.unop).op).symm

/-- **Whiskering pushforwards by a natural transformation is monoidal**: for `τ : F ⟶ F'`, the
natural transformation `F'_* ⟶ F_*` of lax monoidal pushforwards of sheaves is monoidal. -/
instance isMonoidal_sheafPushforwardContinuousNatTrans :
    NatTrans.IsMonoidal (sheafPushforwardContinuousNatTrans τ A J K) where
  unit := ε_comp_sheafPushforwardContinuousNatTrans_app τ A J K
  tensor X Y := μ_comp_sheafPushforwardContinuousNatTrans_app τ A J K X Y

end CategoryTheory.Functor
