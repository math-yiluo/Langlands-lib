/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.AdicSites.Morphism.CompletionMateComparison
public import WeilConjectures.AlgebraicGeometry.Complete.CompleteCoefficientDatumSupplement
import WeilConjectures.CategoryTheory.AdicSites.CompletionUnitFiniteProjection
import all WeilConjectures.AlgebraicGeometry.Constant.ConstantDirectImagePreservesComplete
import WeilConjectures.AlgebraicGeometry.RestrictionSectionCompleteness
import WeilConjectures.CategoryTheory.RingedSiteCompleteElement
import WeilConjectures.CategoryTheory.RingedSiteLocalization
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.Algebra.Category.Grp.FilteredColimits
import WeilConjectures.CategoryTheory.RingedSiteDerivedRestriction
import WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.Algebra.Homology.DerivedInternalHom
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import WeilConjectures.AlgebraicGeometry.RestrictionDerivedProducts
import Mathlib.Algebra.Category.Ring.Limits
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.AlgebraicGeometry.RingedTopoiTensorSections
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import WeilConjectures.Algebra.Homology.Module.ModulePullbackPushforwardAdjunctionSupplement
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.CategoryTheory.DerivedCategory.AdjointFunctors
import Mathlib.CategoryTheory.MorphismProperty.Comma
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantInd
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.CategoryTheory.Limits.Cones
import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantPro
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import WeilConjectures.CategoryTheory.DerivedCategory.EverywhereDefinedDerivedFunctors
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedPointwiseKanBridge
import WeilConjectures.CategoryTheory.DerivedCategory.DerivedAdjunctionCompatibility
import Mathlib.CategoryTheory.Functor.Derived.Adjunction
import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
import WeilConjectures.CategoryTheory.DerivedCategory.ResolvingClassEssentialConstancy
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Homology.KFlatResolution
import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIso
import WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.AlgebraicGeometry.LocalHomTowerCriterion
import WeilConjectures.CategoryTheory.LocalCoefficientLocalization
import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.InternalHom
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import WeilConjectures.Algebra.Homology.LocalCoefficientTelescopeDual
import WeilConjectures.CategoryTheory.Limits.TowerTransitionEndomorphism
import WeilConjectures.Algebra.Homology.HomComplexProjections
import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationIsIso
import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationComm
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHomFree
import WeilConjectures.Algebra.Homology.KInjectiveProductsTermwise
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products
import WeilConjectures.CategoryTheory.Ringed.RingedInternalHomExactRestrictionSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHomCoproduct
import WeilConjectures.CategoryTheory.SequentialTelescopeMono
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Linear
import Mathlib.Algebra.Module.ULift
import Mathlib.RingTheory.Localization.Away.Basic
import WeilConjectures.RingTheory.ModuleLocalizationTowerVanishing
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitExistence

/-! # Finite reduction of the normalized quotient completion

Source: Stacks Tags 099M and 091N; blueprint order 1260.
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false


@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory.AdicSites

private theorem sequential_nilpotent_colimit
    {C : Type*} [Category C] [Preadditive C] [HasColimitsOfShape ℕ C]
    (M : C) (f : M ⟶ M) (k : ℕ) (hf : (End.of f) ^ k = 0) :
    IsZero (colimit (Functor.ofSequence (X := fun _ : ℕ ↦ M) (fun _ ↦ f))) := by
  let F := Functor.ofSequence (X := fun _ : ℕ ↦ M) (fun _ ↦ f)
  have hm (n j : ℕ) : F.map (homOfLE (Nat.le_add_right n j)) = ((End.of f) ^ j).asHom := by
    induction j with
    | zero =>
      simp only [Nat.add_zero, homOfLE_refl, CategoryTheory.Functor.map_id,
        pow_zero, End.one_asHom]
      rfl
    | succ j ih =>
      have he : homOfLE (Nat.le_add_right n (j + 1)) =
          homOfLE (Nat.le_add_right n j) ≫ homOfLE (Nat.le_succ (n + j)) := rfl
      rw [he, CategoryTheory.Functor.map_comp, ih]
      dsimp only [F]
      rw [Functor.ofSequence_map_homOfLE_succ]
      change ((End.of f) ^ j).asHom ≫ f = ((End.of f) ^ (j + 1)).asHom
      rw [pow_succ', End.mul_asHom]
  apply (IsZero.iff_id_eq_zero _).mpr
  apply colimit.hom_ext
  intro n
  have h := colimit.w F (homOfLE (Nat.le_add_right n k))
  rw [hm, hf] at h
  simpa only [End.zero_asHom, zero_comp, Category.comp_id, comp_zero] using h.symm

private theorem sectionLocalization_nilpotent
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) (U : C) (f : R.obj.obj (op U))
    (k : ℕ) (hf : f ^ k = 0) :
    IsZero (ringedSiteSectionLocalization R U f) := by
  let M := SheafOfModules.unit (R.over U)
  let μ : M ⟶ M := M.unitHomEquiv.symm
    (PresheafOfModules.sectionsMk
      (fun V ↦ R.obj.map V.unop.hom.op f)
      (fun {V W} a ↦ ringedSiteSectionLocalization_compatible R U f V W a))
  have hp (j : ℕ) (V : (Over U)ᵒᵖ) (m : R.obj.obj (op V.unop.left)) :
      (((End.of μ) ^ j : End M).asHom.val.app V) m =
        m * (R.obj.map V.unop.hom.op f) ^ j := by
    induction j generalizing m with
    | zero => simp only [pow_zero, End.one_asHom]; exact (mul_one m).symm
    | succ j ih =>
      rw [pow_succ', End.mul_asHom]
      change ((μ.val.app V) ((((End.of μ) ^ j : End M).asHom.val.app V) m)) = _
      rw [ih]
      change (m * (R.obj.map V.unop.hom.op f) ^ j) * R.obj.map V.unop.hom.op f = _
      rw [mul_assoc, ← pow_succ]
  have hμ : (End.of μ) ^ k = 0 := by
    apply End.ext
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro V
    ext
    erw [hp]
    have hz : (R.obj.map V.unop.hom.op f) ^ k = 0 := by
      rw [← map_pow, hf, map_zero]
    rw [hz, mul_zero]
    rfl
  exact sequential_nilpotent_colimit M μ k hμ

open CategoryTheory.Pretriangulated.Opposite in
private theorem completeElement_nilpotent
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (R : Sheaf J CommRingCat.{u})
    [HasDerivedCategory.{u + 1} (ConstantCompletion.Mod R)]
    [∀ U : C, HasDerivedCategory.{u + 1} (SheafOfModules.{u}
      ((siteModuleRings R).over U))]
    (K : DerivedCategory (ConstantCompletion.Mod R)) (U : C)
    (f : R.obj.obj (op U)) (k : ℕ) (hf : f ^ k = 0) :
    IsRingedSiteCompleteElement J R K U f := by
  let O := siteModuleRings R
  let L := (DerivedCategory.singleFunctor (SheafOfModules.{u} (O.over U)) 0).obj
    (ringedSiteSectionLocalization O U f)
  let N := ringedSiteDerivedRestriction O U K
  let : HasDerivedCategory.{u + 1} (ringedSiteModules.{u}
      (siteModuleRings (R.over U))) := inferInstanceAs
    (HasDerivedCategory.{u + 1} (SheafOfModules.{u} (O.over U)))
  obtain ⟨s, hs⟩ := (ringedInternalHom_exact (J.over U) (R.over U)).2 N
  let := s
  have := hs
  have hL : IsZero L := (DerivedCategory.singleFunctor _ 0).map_isZero
    (sectionLocalization_nilpotent O U f k hf)
  exact ((Functor.curry.obj (derivedInternalHom (J.over U) (R.over U))).flip.obj N).map_isZero
    hL.op

private theorem complete_iso (S : Site.{u}) (A : Type u) [CommRing A] (I : Ideal A)
    {M N : S.derived A} (e : M ≅ N) (hM : S.IsComplete A I M) :
    S.IsComplete A I N := by
  intro U f hf
  let : HasDerivedCategory.{u + 1} (SheafOfModules.{u}
      ((siteModuleRings (S.ring A)).over U)) := HasDerivedCategory.standard _
  let H := derivedInternalHom (S.topology.over U) ((S.ring A).over U)
  let L := (DerivedCategory.singleFunctor _ 0).obj
    (ringedSectionLocalization ((S.ring A).over U)
      (ringedSliceSection (S.ring A) U f))
  let eH := H.mapIso ((Iso.refl L).op.prod
    ((ringedDerivedRestriction (S.ring A) U).mapIso e))
  exact (hM U f hf).of_iso eH.symm

private theorem finiteRestriction_complete (S : Site.{u}) (A : Type u) [CommRing A]
    (d : AlgebraicGeometry.Scheme.CompleteCoefficientDatum A) (n : ℕ)
    (M : S.derived (quotientRing A d.ideal n)) :
    S.IsComplete A d.ideal ((S.finiteRestriction A d.ideal n).obj M) := by
  let := d.noetherian
  let R := S.ring A
  let B := S.ring (quotientRing A d.ideal n)
  let φ := ConstantCompletion.quotient S.topology A d.ideal n
  let : HasDerivedCategory.{u + 1} (ConstantCompletion.Mod R) :=
    HasDerivedCategory.standard _
  let : HasDerivedCategory.{u + 1} (ConstantCompletion.Mod B) :=
    HasDerivedCategory.standard _
  let : ∀ U : S.objects, HasDerivedCategory.{u + 1}
      (SheafOfModules.{u} ((siteModuleRings R).over U)) :=
    fun _ ↦ HasDerivedCategory.standard _
  let : ∀ U : S.objects, HasDerivedCategory.{u + 1}
      (SheafOfModules.{u} ((siteModuleRings B).over U)) :=
    fun _ ↦ HasDerivedCategory.standard _
  let P := DerivedCategory.Q.objPreimage M
  let L := (ConstantCompletion.Q R).obj
    (((ConstantCompletion.res φ).mapHomologicalComplex (.up ℤ)).obj P)
  have hL : S.IsComplete A d.ideal L := by
    apply (ConstantCompletion.complete_iff_constantElements S.topology A d.ideal L).mpr
    intro a ha U
    apply (restrictScalars_completeElement_iff S.topology R B φ M U _).mpr
    apply completeElement_nilpotent S.topology B M U _ (n + 1)
    rw [← map_pow]
    apply RingHom.mem_ker.mp
    rw [(ConstantCompletion.flat_and_quotients S.topology A d.ideal).2.2 n U |>.2]
    apply Ideal.subset_span
    refine ⟨⟨a ^ (n + 1), Ideal.pow_mem_pow ha (n + 1)⟩, ?_⟩
    simp only [ConstantCompletion.constantSection, map_pow]
  let e : L ≅ (S.finiteRestriction A d.ideal n).obj M :=
    (ConstantCompletion.resFactors φ).app P ≪≫
      (ConstantCompletion.dres φ).mapIso (DerivedCategory.Q.objObjPreimageIso M)
  exact complete_iso S A d.ideal e hL

end CategoryTheory.AdicSites
