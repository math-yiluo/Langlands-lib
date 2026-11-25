/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.RingedKoszulSystem
import WeilConjectures.Algebra.Homology.InternalHom
import WeilConjectures.CategoryTheory.RingedKoszulFactorColimit

/-! The augmentation-compatible colimit identification for the ringed Koszul system.
Source: Stacks Project, More on Algebra, Tag 0913.
(auxiliary; not a blueprint node).
(auxiliary; not a blueprint node)
-/

@[expose] public noncomputable section

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
variable (O : Sheaf J CommRingCat.{u}) (r : ℕ)
variable (b : Fin r → (O.obj ⋙ forget CommRingCat).sections)

set_option synthInstance.maxSize 2048 in
set_option backward.isDefEq.respectTransparency false in
/-- The colimit of the positive ringed Koszul system is the extended Cech complex,
compatibly with the augmentation. The one-section fraction cocone is a colimit;
tensoring its factors and restricting to the final diagonal gives the finite-list colimit.
(auxiliary; not a blueprint node).
Proof: identify the one-section colimit by fractions, then induct over the ordered tensor factors.
Tensor preserves colimits by its right adjoint, and the diagonal of the filtered index is final.
The factor augmentation equations combine by tensor naturality; uniqueness of colimits gives
the required isomorphism and its augmentation equation. -/
theorem exists_ringed_cech_koszul_colimit_iso :
    ∃ alpha : colimit (ringedKoszulDiagram O r b) ≅ (ringedExtendedCech O r b).1,
      alpha.hom ≫ (ringedExtendedCech O r b).2 =
        colimit.desc _ (ringedKoszulAugmentationCocone O r b) := by
  let : IsGrothendieckAbelian.{u} (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)) :=
    SheafOfModules.isGrothendieckAbelian _
  let := SheafOfModules.monoidalCategory O
  let := SheafOfModules.symmetricCategory O
  let := Classical.choice (SheafOfModules.tensorClosed O).1
  let := Classical.choice (SheafOfModules.tensorClosed O).2.1
  let A := SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)
  have (X : A) : PreservesColimitsOfSize.{0, 0} (MonoidalCategory.tensorRight X) :=
    preservesColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight X)
  have (K : CochainComplex A ℤ) :
      PreservesColimitsOfSize.{0, 0} (MonoidalCategory.tensorLeft K) :=
    (CochainComplex.tensorHomAdjunction K).leftAdjoint_preservesColimits
  have (K : CochainComplex A ℤ) :
      PreservesColimitsOfSize.{0, 0} (MonoidalCategory.tensorRight K) :=
    preservesColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight K)
  have (K : ringedSiteComplex O) :
      PreservesColimitsOfSize.{0, 0} ((ringedKoszulTensor O).obj K) := by
    apply preservesColimits_of_natIso
      (F := MonoidalCategory.tensorLeft K)
    exact NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; rfl)
  have (K : ringedSiteComplex O) :
      PreservesColimitsOfSize.{0, 0} ((ringedKoszulTensor O).flip.obj K) := by
    apply preservesColimits_of_natIso
      (F := MonoidalCategory.tensorRight K)
    exact NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; rfl)
  have h (r : ℕ) (b : Fin r → (O.obj ⋙ forget CommRingCat).sections) :
      ∃ ι : ringedKoszulDiagram O r b ⟶
          (Functor.const ℕ).obj (ringedExtendedCech O r b).1,
        Nonempty (IsColimit (Cocone.mk _ ι)) ∧
          ∀ m, ι.app m ≫ (ringedExtendedCech O r b).2 =
            ringedKoszulProjection O r b m := by
    induction r with
    | zero =>
      refine ⟨𝟙 _, ⟨?_⟩, ?_⟩
      · exact isColimitConstCocone _ _
      · intro m
        simp [ringedExtendedCech, ringedKoszulProjection]
    | succ r ih =>
      obtain ⟨ι, ⟨hι⟩, hιa⟩ := exists_ringedKoszulFactor_colimit O (b 0)
      obtain ⟨κ, ⟨hκ⟩, hκa⟩ := ih (fun i ↦ b i.succ)
      let c := ((ringedKoszulTensor O).mapCocone₂
        (Cocone.mk _ ι) (Cocone.mk _ κ)).whisker (Functor.diag ℕ)
      have hc : IsColimit c :=
        (Functor.Final.isColimitWhiskerEquiv (Functor.diag ℕ) _).symm
          (isColimitOfPreserves₂ (ringedKoszulTensor O) hι hκ)
      refine ⟨c.ι, ⟨hc⟩, ?_⟩
      intro m
      have ha : (ringedExtendedCech O (r + 1) b).2 =
          ((ringedKoszulTensor O).map
            (ringedLocalizationTwoTermAugmentation O (b 0))).app _ ≫
          ((ringedKoszulTensor O).obj _).map (ringedExtendedCech O r _).2 ≫
          (ringedKoszulUnitTensorIso O).hom := by
        change HomologicalComplex.tensorHom _ _ ≫ _ = _
        simp only [ringedKoszulTensor, Functor.map₂HomologicalComplex,
          HomologicalComplex.tensorHom, HomologicalComplex.mapBifunctorMap,
          Functor.map_id, NatTrans.id_app, Category.id_comp, Category.comp_id,
          HomologicalComplex₂.total.map_comp, Category.assoc]
        rfl
      rw [ha]
      change (((ringedKoszulTensor O).map (ι.app m)).app _ ≫
        ((ringedKoszulTensor O).obj _).map (κ.app m)) ≫
        (((ringedKoszulTensor O).map (ringedLocalizationTwoTermAugmentation O (b 0))).app _ ≫
          ((ringedKoszulTensor O).obj _).map (ringedExtendedCech O r _).2 ≫
          (ringedKoszulUnitTensorIso O).hom) = _
      simp only [Category.assoc]
      rw [NatTrans.naturality_assoc, ← NatTrans.comp_app_assoc,
        ← Functor.map_comp, hιa, ← Functor.map_comp_assoc, hκa]
      rfl
  obtain ⟨ι, ⟨hι⟩, hιa⟩ := h r b
  let e := (colimit.isColimit (ringedKoszulDiagram O r b)).coconePointUniqueUpToIso hι
  refine ⟨e, ?_⟩
  apply colimit.hom_ext
  intro m
  change (colimit.cocone _).ι.app m ≫ e.hom ≫ _ = _
  rw [← Category.assoc]
  erw [IsColimit.comp_coconePointUniqueUpToIso_hom]
  exact (hιa m).trans (colimit.ι_desc (ringedKoszulAugmentationCocone O r b) m).symm

end CategoryTheory
