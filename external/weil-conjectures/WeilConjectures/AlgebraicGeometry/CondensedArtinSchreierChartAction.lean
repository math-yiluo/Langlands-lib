/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedArtinSchreierProductChart
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedDeckEvaluation
import WeilConjectures.CategoryTheory.ModuleObjects.ModuleGlobalSectionsMonoidalLinear

/-! # Translation and the origin in the Artin–Schreier product chart -/

@[expose] public noncomputable section

set_option autoImplicit false
set_option quotPrecheck false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] (k : Type u) [Field k] [Fintype k]

local notation "q" => AffineSpace.artinSchreierMap PUnit (Spec (CommRingCat.of k))
  (Fintype.card k)

omit [IsCommMonObj Λ] in
private theorem lowerStarCongr_app_eq
    {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g)
    (N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    (CondensedRing.lowerStarCongr Λ h).hom.app N =
      eqToHom (congrArg (fun t ↦ (CondensedRing.lowerStar Λ t).obj N) h) := by
  subst g
  rfl

private theorem translation_deck_eq (a : k) :
    condensedArtinSchreierTranslationAction Λ k a =
      CondensedRing.regularDeckEnd Λ q (Etale.artinSchreierTranslation k a)
        (Etale.artinSchreierTranslation_comp_artinSchreierMap k a) := by
  simp only [condensedArtinSchreierTranslationAction, CondensedRing.regularDeckEnd,
    lowerStarCongr_app_eq]

private theorem normalized_deck_evaluation
    {X Y P : Scheme.{u}} (f : X ⟶ Y) (g : X ⟶ X) (hg : g ≫ f = f)
    (v : P ⟶ Y) (t : P ⟶ X) (ht : t ≫ f = v) :
    (CondensedRing.upperStar Λ v).map (CondensedRing.regularDeckEnd Λ f g hg).asHom ≫
        condensedRegularSheetProjection Λ f v t ht =
      condensedRegularSheetProjection Λ f v (t ≫ g)
        (show (t ≫ g) ≫ f = v by rw [Category.assoc, hg, ht]) := by
  simpa only [condensedRegularSheetProjection, Mod.regularMapIso_hom,
    Mod.tensorUnit_eq_regular, Category.assoc] using
    CondensedRing.regularDeckEnd_evaluation Λ f g hg v t ht

private theorem abstract_identity_evaluation
    {C : Type*} {D : Type*} [Category C] [Category D]
    {F : C ⥤ D} {G : D ⥤ C} {H : D ⥤ D}
    (ε : G ⋙ F ⟶ 𝟭 D) (I : H ≅ 𝟭 D) (θ : F ≅ F ⋙ H)
    (hθ : θ = F.rightUnitor.symm ≪≫ Functor.isoWhiskerLeft F I.symm) (M : D) :
    θ.hom.app (G.obj M) ≫ H.map (ε.app M) ≫ I.hom.app M = ε.app M := by
  rw [hθ]
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.rightUnitor_inv_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Iso.symm_hom, Category.id_comp]
  have hn := I.inv.naturality (ε.app M)
  simp only [Functor.id_map, Functor.id_obj] at hn
  rw [← reassoc_of% hn, Iso.inv_hom_id_app]
  exact Category.comp_id (ε.app M)

private theorem identity_sheet_comparison
    {X Y : Scheme.{u}} (f : X ⟶ Y) (hw : 𝟙 X ≫ f = f) :
    CondensedRing.upperStarCongr Λ hw.symm ≪≫
        CondensedRing.upperStarComp Λ (𝟙 X) f =
      (CondensedRing.upperStar Λ f).rightUnitor.symm ≪≫
        Functor.isoWhiskerLeft (CondensedRing.upperStar Λ f)
          (CondensedRing.upperStarId Λ X).symm := by
  rw [CondensedRing.upperStarComp_id_left]
  have hh : CondensedRing.upperStarCongr Λ hw.symm ≪≫
      CondensedRing.upperStarCongr Λ (Category.id_comp f) =
        Iso.refl (CondensedRing.upperStar Λ f) := by
    apply Iso.ext
    apply NatTrans.ext
    funext M
    simp only [Iso.trans_hom, NatTrans.comp_app, Iso.refl_hom, NatTrans.id_app]
    rw [CondensedRing.upperStarCongr_hom_app_trans, CondensedRing.upperStarCongr_self]
    rfl
  calc
    _ = (CondensedRing.upperStarCongr Λ hw.symm ≪≫
        CondensedRing.upperStarCongr Λ (Category.id_comp f)) ≪≫
      ((CondensedRing.upperStar Λ f).rightUnitor.symm ≪≫
        Functor.isoWhiskerLeft (CondensedRing.upperStar Λ f)
          (CondensedRing.upperStarId Λ X).symm) := by simp only [Iso.trans_assoc]
    _ = _ := by rw [hh, Iso.refl_trans]

private theorem unit_identity_sheet
    {X Y : Scheme.{u}} (f : X ⟶ Y) (s : X ⟶ X)
    (hs : s = 𝟙 X) (hw : s ≫ f = f) :
    CondensedRing.stalkLowerStarProj Λ hw (𝟙_ _) ≫
      (Functor.Monoidal.εIso (CondensedRing.upperStar Λ s)).inv =
    (CondensedRing.upperStarLowerStarAdjunction Λ f).counit.app (𝟙_ _) := by
  subst s
  have h := abstract_identity_evaluation
    (CondensedRing.upperStarLowerStarAdjunction Λ f).counit
    (CondensedRing.upperStarId Λ X)
    (CondensedRing.upperStarCongr Λ hw.symm ≪≫
      CondensedRing.upperStarComp Λ (𝟙 X) f)
    (identity_sheet_comparison Λ f hw) (𝟙_ _)
  rw [CondensedRing.upperStarId_hom_app_unit] at h
  simpa only [CondensedRing.stalkLowerStarProj_eq, Iso.trans_hom,
    NatTrans.comp_app, Category.assoc] using h

private theorem regular_identity_sheet
    {X Y : Scheme.{u}} (f : X ⟶ Y) (s : X ⟶ X)
    (hs : s = 𝟙 X) (hw : s ≫ f = f) :
    condensedRegularSheetProjection Λ f f s hw =
      (CondensedRing.upperStarLowerStarAdjunction Λ f).counit.app
        (Mod.regular (condensedRingObj Λ X)) := by
  simpa only [condensedRegularSheetProjection, Mod.regularMapIso_hom,
    Mod.tensorUnit_eq_regular] using unit_identity_sheet Λ f s hs hw

/-- Translations permute the sheet evaluations by addition.

Source: latest blueprint `prop-kernel-lisse.proof.md`, the character chart
(blueprint: lem-kernel-condensed-chart-action).

Proof. The defining translation is the regular-module deck pullback. Evaluation after
this pullback is evaluation on the composite sheet, by the adjunction and composition
coherence formula. The composite of translations by a and c is translation by a+c.
The equality of coefficient unit comparisons under the same transport gives the stated
normalized sheet evaluation, including c=0 and characteristic two. -/
theorem condensedArtinSchreierChart_translation (a c : k) :
    (CondensedRing.upperStar Λ q).map
        (condensedArtinSchreierTranslationAction Λ k c).asHom ≫
      condensedArtinSchreierChartProjection Λ k a =
    condensedArtinSchreierChartProjection Λ k (a + c) := by
  rw [translation_deck_eq]
  have h := normalized_deck_evaluation Λ q (Etale.artinSchreierTranslation k c)
    (Etale.artinSchreierTranslation_comp_artinSchreierMap k c) q
    (Etale.artinSchreierTranslation k a)
    (Etale.artinSchreierTranslation_comp_artinSchreierMap k a)
  simpa only [condensedArtinSchreierChartProjection,
    ← Etale.artinSchreierTranslation_add] using h

/-- Evaluation on the zero-labelled sheet is the adjunction counit.

Source: latest blueprint `prop-kernel-lisse.proof.md`, evaluation at zero
(blueprint: lem-kernel-condensed-chart-action).

Proof. Translation by zero is the identity morphism. In the sheet restriction formula,
the identity-composition comparison is the inverse of the identity-pullback comparison.
Naturality moves that comparison across the counit. At the coefficient unit it is the
inverse strong-monoidal unit comparison, so the two comparisons cancel. -/
theorem condensedArtinSchreierChart_zero :
    condensedArtinSchreierChartProjection Λ k 0 =
      (CondensedRing.upperStarLowerStarAdjunction Λ q).counit.app
        (Mod.regular (condensedRingObj Λ (AffineSpace PUnit (Spec (.of k))))) := by
  simpa only [condensedArtinSchreierChartProjection] using
    regular_identity_sheet Λ q (Etale.artinSchreierTranslation k 0)
      (Etale.artinSchreierTranslation_zero k)
      (Etale.artinSchreierTranslation_comp_artinSchreierMap k 0)

end AlgebraicGeometry.ProEtale
