/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Ringed.RingedPresentationData
import WeilConjectures.CategoryTheory.Ringed.RingedEquivalenceModuleHom
import WeilConjectures.CategoryTheory.ScalarLocalizationRegularColimit
import WeilConjectures.CategoryTheory.RingedSectionLocalization
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.RingTheory.Localization.Away.Basic
import WeilConjectures.Algebra.Homology.DerivedInternalHom
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Functor.OfSequence
import WeilConjectures.RingTheory.ModuleLocalizationFilteredColimit
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
import Mathlib.Algebra.Module.LocalizedModule.IsLocalization
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
import WeilConjectures.CategoryTheory.Ringed.RingedGeneralizedCompletenessCriterion
import all WeilConjectures.CategoryTheory.Ringed.RingedEquivalenceSlices
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp

/-! # Generalized localization tests on a ringed site -/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false


@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.MonoidalCategory
namespace CategoryTheory
attribute [local instance] ringSections

private theorem sequence_colimit_transport
    {A B : Type*} [Category* A] [Category* B]
    (F : A ⥤ B) [PreservesColimitsOfShape ℕ F]
    {X : A} {Y : B} (f : X ⟶ X) (g : Y ⟶ Y)
    (i : F.obj X ≅ Y) (h : F.map f ≫ i.hom = i.hom ≫ g)
    (c : Cocone (Functor.ofSequence (X := fun _ : ℕ ↦ X) (fun _ ↦ f)))
    (d : Cocone (Functor.ofSequence (X := fun _ : ℕ ↦ Y) (fun _ ↦ g)))
    (hc : IsColimit c) (hd : IsColimit d) :
    ∃ q : F.obj c.pt ≅ d.pt,
      F.map (c.ι.app 0) ≫ q.hom = i.hom ≫ d.ι.app 0 := by
  let α : Functor.ofSequence (X := fun _ : ℕ ↦ X) (fun _ ↦ f) ⋙ F ⟶
      Functor.ofSequence (X := fun _ : ℕ ↦ Y) (fun _ ↦ g) :=
    NatTrans.ofSequence (fun _ ↦ i.hom) (by
      intro n
      dsimp only [Functor.comp_map]
      rw [Functor.ofSequence_map_homOfLE_succ, Functor.ofSequence_map_homOfLE_succ]
      exact h)
  have : IsIso α := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro n
    change IsIso i.hom
    infer_instance
  exact ⟨(isColimitOfPreserves F hc).coconePointsIsoOfNatIso hd (asIso α),
    IsColimit.comp_coconePointsIsoOfNatIso_hom
      (isColimitOfPreserves F hc) hd (asIso α) 0⟩

private theorem localization_transport
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {R : Sheaf J CommRingCat.{u}} {S : Sheaf K CommRingCat.{u}}
    (F : PresentationModules R ⥤ PresentationModules S)
    [PreservesColimitsOfShape ℕ F]
    (i : F.obj (SheafOfModules.unit (localCoefficientRings R)) ≅
      SheafOfModules.unit (localCoefficientRings S))
    (s : (R.obj ⋙ forget CommRingCat).sections)
    (t : (S.obj ⋙ forget CommRingCat).sections)
    (h : F.map (presentationScalar R s) ≫ i.hom = i.hom ≫ presentationScalar S t) :
    ∃ l : F.obj (ringedSectionLocalizationOfUniverses R s) ≅
        ringedSectionLocalizationOfUniverses S t,
      F.map (ringedSectionLocalizationUnit R s) ≫ l.hom =
        i.hom ≫ ringedSectionLocalizationUnitOfUniverses S t := by
  change ∃ l : F.obj (ringedSectionLocalization R s) ≅ ringedSectionLocalization S t,
    F.map (ringedSectionLocalizationUnit R s) ≫ l.hom =
      i.hom ≫ ringedSectionLocalizationUnit S t
  have scalar_eq {E : Type u} [SmallCategory E] {L : GrothendieckTopology E}
      (T : Sheaf L CommRingCat.{u}) (a : (T.obj ⋙ forget CommRingCat).sections) :
      presentationScalar T a = (SheafOfModules.unitHomEquiv _).symm
        ⟨a.val, a.property⟩ := by
    apply (SheafOfModules.unitHomEquiv _).injective
    rw [Equiv.apply_symm_apply]
    ext U
    change (a.val U : T.obj.obj U) * 1 = a.val U
    exact mul_one _
  obtain ⟨c, ⟨hc⟩, ec, hec⟩ := scalarLocalization_regularColimit R s
  obtain ⟨d, ⟨hd⟩, ed, hed⟩ := scalarLocalization_regularColimit S t
  rw [scalar_eq R s, scalar_eq S t] at h
  obtain ⟨q, hq⟩ := sequence_colimit_transport F _ _ i h c d hc hd
  refine ⟨(F.mapIso ec).symm ≪≫ q ≪≫ ed, ?_⟩
  have hc0 : F.map (ringedSectionLocalizationUnit R s) ≫ F.map ec.inv =
      F.map (c.ι.app 0) := by
    exact (F.map_comp _ _).symm.trans
      (congrArg F.map ((Iso.comp_inv_eq ec).mpr hec.symm))
  change F.map (ringedSectionLocalizationUnit R s) ≫
    ((F.map ec.inv ≫ q.hom) ≫ ed.hom) = _
  rw [← Category.assoc, ← Category.assoc, hc0, Category.assoc, reassoc_of% hq, hed]

private def inverseHomComparison
    {A B : Type*} [Category A] [Category B] (E : A ≌ B)
    (H : Aᵒᵖ × A ⥤ A) (K : Bᵒᵖ × B ⥤ B)
    (a : H ⋙ E.functor ≅ (E.functor.op.prod E.functor) ⋙ K) :
    K ⋙ E.inverse ≅ (E.inverse.op.prod E.inverse) ⋙ H :=
  (Iso.isoCompInverse (H := E)
    (Functor.associator _ _ _ ≪≫
      Iso.inverseCompIso (G := E.op.prod E) a)).symm

end CategoryTheory
