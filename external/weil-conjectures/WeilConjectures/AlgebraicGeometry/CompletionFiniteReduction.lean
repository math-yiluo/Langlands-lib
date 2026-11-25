/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Homology.KFlatTotalTensorModel
public import WeilConjectures.AlgebraicGeometry.CompleteCoefficientDatum
public import WeilConjectures.AlgebraicGeometry.CompletedPullbackAdjunction
public import WeilConjectures.AlgebraicGeometry.ConstantPullbackScalar
public import WeilConjectures.AlgebraicGeometry.DerivedPullbackRepresentativeComputation
public import WeilConjectures.AlgebraicGeometry.LocalCompletenessModels
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedPullbackComposition
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImageTensorComparison
public import WeilConjectures.AlgebraicGeometry.ResolvingRepresentativeWhiskering
public import WeilConjectures.AlgebraicGeometry.RestrictionSectionCompleteness
public import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.ResolvingClassEssentialConstancy
public import WeilConjectures.CategoryTheory.LeftDerivedKanSourceTriangles
public import WeilConjectures.CategoryTheory.LocalizedModuleExactForSystems
public import WeilConjectures.CategoryTheory.ModulePullbackPushforwardAdjunction
public import WeilConjectures.CategoryTheory.RightKanExtensionCoherentShift
public import WeilConjectures.CategoryTheory.RingedSiteCompleteElementsIdeal
public import WeilConjectures.Mathlib.Algebra.Homology.BifunctorShift
public import WeilConjectures.SecSmoothPurity.CochainComparisonMonoidalEquations
public import WeilConjectures.SecSmoothPurity.CochainPullbackTensorCoherence
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

set_option linter.privateModule false

/-! # Finite reduction of the normalized quotient completion

Source: Stacks Tags 099M and 091N; blueprint order 1260.
-/

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

end CategoryTheory.AdicSites
