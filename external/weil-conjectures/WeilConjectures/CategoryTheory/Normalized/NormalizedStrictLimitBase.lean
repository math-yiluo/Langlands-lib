/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import WeilConjectures.CategoryTheory.Triangulated.HomotopyLimit

import WeilConjectures.CategoryTheory.Triangulated.HomotopyLimit.Exists
import all WeilConjectures.CategoryTheory.RingedStrictTowerHomotopyLimit
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian
import all WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all Mathlib.CategoryTheory.Triangulated.Functor
import all Mathlib.Algebra.Homology.Functor
import all Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import all Mathlib.CategoryTheory.Functor.Derived.RightDerived
import all Mathlib.CategoryTheory.Whiskering
import all Mathlib.CategoryTheory.Functor.OfSequence
import all Mathlib.CategoryTheory.Limits.Shapes.Countable
import all Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import all WeilConjectures.Algebra.Homology.KInjectiveProductsTermwise
import all Mathlib.Algebra.Homology.HomologicalComplexLimits
import all Mathlib.Algebra.Homology.DerivedCategory.KInjective
import all WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import all WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products
import all WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
import all Mathlib.CategoryTheory.Adjunction.Evaluation
import all WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import all Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
import all Mathlib.Algebra.BigOperators.Ring.Finset

/-! # The ordinary normalization of the derived strict-limit cone

Source: Stacks Project, sites-cohomology.tex, Tags 0940 and 0941.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe a v w g
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
namespace CategoryTheory
open RingedStrictTowerProof RingedStrictTowerProof.CoreWork

private theorem roos_normalization
    {A : Type a} [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{g} A]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ A)]
    [HasLimitsOfShape ℕᵒᵖ A] [HasCountableProducts A]
    [HasCountableProducts (DerivedCategory A)]
    [IsGrothendieckAbelian.{g} (ℕᵒᵖ ⥤ A)]
    (RF : DerivedCategory (ℕᵒᵖ ⥤ A) ⥤ DerivedCategory A)
    (η : L ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RF)
    (hI : ∀ I, CochainComplex.IsKInjective I → IsIso (η.app I))
    (E : DerivedCategory (ℕᵒᵖ ⥤ A) ⥤ (ℕᵒᵖ ⥤ DerivedCategory A))
    (ε : DerivedCategory.Q ⋙ E ≅ evQ) (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    η.app X ≫ (pNat RF η hI E ε).app (DerivedCategory.Q.obj X) ≫
        DP.map (ε.hom.app X) = DerivedCategory.Q.map (inc.app X) ≫ pc.app X := by
  let qX := q.app X
  have hq : QuasiIso qX := q_quasiIso X
  have hqi (n : ℕᵒᵖ) : IsIso ((evQ.map qX).app n) := by
    change IsIso (DerivedCategory.Q.map
      ((((evaluation ℕᵒᵖ A).obj n).mapHomologicalComplex (.up ℤ)).map qX))
    infer_instance
  have : IsIso (evQ.map qX) := NatIso.isIso_of_isIso_app _
  let ai := (aIso RF η hI).app X
  let bi := (bIso E ε).app X
  have haihom : ai.hom = η.app (F.obj X) ≫
      inv (RF.map (DerivedCategory.Q.map qX)) := by
    simp [ai, qX]
  have hai : η.app X ≫ ai.inv = DerivedCategory.Q.map (L.map qX) := by
    apply (cancel_mono ai.hom).1
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, haihom]
    have hn := η.naturality qX
    change DerivedCategory.Q.map (L.map qX) ≫ η.app (F.obj X) =
      η.app X ≫ RF.map (DerivedCategory.Q.map qX) at hn
    rw [← Category.assoc, hn]
    simp
  have hbi : bi.hom = pc.app (F.obj X) ≫
      DP.map (inv (evQ.map qX) ≫ ε.inv.app X) := by
    simp [bi, qX, Limits.Pi.map_comp_map]
  have hb : DerivedCategory.Q.map (P.map qX) ≫ bi.hom ≫
      DP.map (ε.hom.app X) = pc.app X := by
    have hn := pc.naturality qX
    change DerivedCategory.Q.map (P.map qX) ≫ pc.app (F.obj X) =
      pc.app X ≫ DP.map (evQ.map qX) at hn
    rw [hbi]
    simp only [← Category.assoc]
    rw [hn]
    simp only [Category.assoc, ← DP.map_comp, IsIso.hom_inv_id_assoc,
      Iso.inv_hom_id_app]
    simp only [DP, NatTrans.id_app, Limits.Pi.map_id]
    exact Category.comp_id _
  rw [pNat_app]
  change η.app X ≫ (ai.inv ≫ DerivedCategory.Q.map (inc.app (F.obj X)) ≫ bi.hom) ≫
    DP.map (ε.hom.app X) = _
  calc
    _ = (η.app X ≫ ai.inv) ≫ DerivedCategory.Q.map (inc.app (F.obj X)) ≫
        bi.hom ≫ DP.map (ε.hom.app X) := by simp only [Category.assoc]
    _ = DerivedCategory.Q.map (L.map qX ≫ inc.app (F.obj X)) ≫
        bi.hom ≫ DP.map (ε.hom.app X) := by
      rw [hai, CategoryTheory.Functor.map_comp]
      simp only [Category.assoc]
    _ = DerivedCategory.Q.map (inc.app X ≫ P.map qX) ≫
        bi.hom ≫ DP.map (ε.hom.app X) := by
      have hn := inc.naturality qX
      change L.map qX ≫ inc.app (F.obj X) = inc.app X ≫ P.map qX at hn
      rw [hn]
    _ = DerivedCategory.Q.map (inc.app X) ≫ pc.app X := by
      rw [Functor.map_comp, Category.assoc, hb]

/-- The Milnor cone of a total derived strict inverse limit retains the ordinary
limit projections under its specified derived comparison.

Source: Stacks Project, sites-cohomology.tex, Tags 0940 and 0941
(blueprint: lem-sfb-normalized-strict-limit-base).
Proof: use the natural short-exact Roos triangle on a functorial injective resolution.
The formula for its first arrow cancels the evaluated resolution and the product
comparison, giving the ordinary projections. Uniqueness of total derived functors
transports the triangle and the normalization to the supplied comparison. -/
theorem normalizedStrictLimitBase
    {A : Type a} [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{g} A]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ A)]
    [HasLimitsOfShape ℕᵒᵖ A] [HasCountableProducts A]
    [HasCountableProducts (DerivedCategory A)]
    (R : DerivedCategory (ℕᵒᵖ ⥤ A) ⥤ DerivedCategory A)
    (η : (lim : (ℕᵒᵖ ⥤ A) ⥤ A).mapHomologicalComplex (.up ℤ) ⋙
      DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ R)
    (hR : R.IsRightDerivedFunctor η
      (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ A) (.up ℤ)))
    (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    ∃ p : (Functor.const ℕᵒᵖ).obj (R.obj (DerivedCategory.Q.obj X)) ⟶
        X.asFunctor ⋙ DerivedCategory.Q,
      IsHomotopyLimit (Cone.mk _ p) ∧
      ∀ n : ℕ, η.app X ≫ p.app (op n) = DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex (lim.π (op n)) (.up ℤ)).app X) := by
  let : IsGrothendieckAbelian.{g} (ℕᵒᵖ ⥤ A) := tower_grothendieck A
  have : (lim : (ℕᵒᵖ ⥤ A) ⥤ A).Additive :=
    Functor.additive_of_preserves_binary_products _
  obtain ⟨RF, ηF, hRF, hI, -, -⟩ := totalDerivedData (lim : (ℕᵒᵖ ⥤ A) ⥤ A)
  have := hRF
  have := hR
  let d := Functor.rightDerivedUnique RF R ηF η
    (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ A) (.up ℤ))
  obtain ⟨E, ⟨ε⟩⟩ := evaluationData (A := A)
  let p := (pNat RF ηF hI E ε).app (DerivedCategory.Q.obj X)
  let δ := (deltaNat RF ηF hI E ε).app (DerivedCategory.Q.obj X)
  let PE : Fan (fun n : ℕ ↦ (E.obj (DerivedCategory.Q.obj X)).obj (op n)) :=
    Fan.mk _ (Pi.π _)
  let hPE : IsLimit PE := productIsProduct _
  have ht : towerTransitionEndomorphism
      (fun n : ℕ ↦ (E.obj (DerivedCategory.Q.obj X)).map (homOfLE n.le_succ).op) =
        𝟙 PE.pt - towerShift hPE := by
    apply Fan.IsLimit.hom_ext hPE
    intro n
    rw [Preadditive.sub_comp]
    erw [Category.id_comp, towerShift_proj]
    simp [towerTransitionEndomorphism, towerProductShift, PE]
  have hT : Triangle.mk p (𝟙 PE.pt - towerShift hPE) δ ∈ distTriang _ := by
    have h := roos_Q RF ηF hI E ε X
    change Triangle.mk p _ δ ∈ distTriang _ at h
    rw [ht] at h
    exact h
  let cE := coneOfComp hPE p (comp_towerShift_of_distinguished hPE hT)
  have hcE : IsHomotopyLimit cE := isHomotopyLimit_coneOfComp hPE hT
  let c := ((Cone.postcompose (ε.app X).hom).obj cE).extend
    (d.app (DerivedCategory.Q.obj X)).inv
  have hc : IsHomotopyLimit c := hcE.of_iso (ε.app X) c
    (d.app (DerivedCategory.Q.obj X)) (by intro n; simp [c])
  refine ⟨c.π, hc, ?_⟩
  intro n
  have hd : ηF.app X ≫ d.hom.app (DerivedCategory.Q.obj X) = η.app X := by
    simpa only [d, Functor.rightDerivedUnique, Functor.rightDerivedNatIso_hom,
      Iso.refl_hom, NatTrans.id_app, Category.id_comp] using
      Functor.rightDerivedNatTrans_app RF R ηF η
        (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ A) (.up ℤ)) (𝟙 _) X
  have hn := congrArg (fun f ↦ f ≫ Pi.π
    (fun n : ℕ ↦ DerivedCategory.Q.obj (X.asFunctor.obj (op n))) n)
      (roos_normalization RF ηF hI E ε X)
  dsimp only [DP, CategoryTheory.Functor.comp_obj] at hn
  simp only [Category.assoc] at hn
  erw [Limits.Pi.map_π] at hn
  simp only [piComparison_comp_π, ← DerivedCategory.Q.map_comp, Pi.lift_comp_π] at hn
  rw [← hd]
  change (ηF.app X ≫ d.hom.app (DerivedCategory.Q.obj X)) ≫
    (d.inv.app (DerivedCategory.Q.obj X) ≫
      ((p ≫ Pi.π _ n) ≫ (ε.hom.app X).app (op n))) = _
  rw [Category.assoc, Iso.hom_inv_id_app_assoc]
  simpa only [Category.assoc, p, evQ, CategoryTheory.Functor.comp_obj] using hn

end CategoryTheory
