/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.System.SystemLevelLeftExtensionBasic
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-! # Exact derived subsequence comparisons

Source: Zheng, Construction 4.1; Stacks 015F.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u v w
open CategoryTheory CategoryTheory.Limits Opposite
namespace SheafOfModules
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
  (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w})

/-- Derived subsequence restriction followed by evaluation is the actual selected evaluation.
Source: Stacks 015F (blueprint: lem-pur-system-derived-subsequence). -/
def systemDerivedSubsequenceEvaluation (r : ℕ ↪o ℕ) (n : ℕ) :
    derivedSystemSubsequence B r ⋙ derivedSystemEvaluation (selectedSystemRings B r) n ≅
      derivedSystemEvaluation B (r n) :=
  Functor.mapDerivedCategoryCompIso (systemSubsequence B r)
    (systemEvaluation (selectedSystemRings B r) n)

/-- The selected-evaluation comparison has the canonical cochain representative formula.
Source: Stacks 015F (blueprint: lem-pur-system-derived-subsequence).
Proof: compose with the exact-functor compositor in the opposite direction, then apply
its factorization equation. The compositor and its inverse cancel. -/
theorem systemDerivedSubsequenceEvaluation_rep (r : ℕ ↪o ℕ) (n : ℕ)
    (K : CochainComplex (StrictRingSystem B) ℤ) :
    (systemDerivedSubsequenceEvaluation B r n).hom.app (DerivedCategory.Q.obj K) ≫
      (systemEvaluation B (r n)).mapDerivedCategoryFactors.hom.app K =
    (derivedSystemEvaluation (selectedSystemRings B r) n).map
      ((systemSubsequence B r).mapDerivedCategoryFactors.hom.app K) ≫
    (systemEvaluation (selectedSystemRings B r) n).mapDerivedCategoryFactors.hom.app
      (((systemSubsequence B r).mapHomologicalComplex (.up ℤ)).obj K) := by
  let e := Functor.mapDerivedCategoryCompIso (systemSubsequence B r)
    (systemEvaluation (selectedSystemRings B r) n)
  apply (cancel_epi (e.inv.app (DerivedCategory.Q.obj K))).1
  change e.inv.app _ ≫ (e.hom.app _ ≫ _) = _
  erw [Iso.inv_hom_id_app_assoc]
  exact (Functor.mapDerivedCategoryCompIso_hom_app_factors
    (systemSubsequence B r) (systemEvaluation (selectedSystemRings B r) n) K).symm

/-- Successive derived restrictions are the exact restriction along the composite selection.
Source: Stacks 015F (blueprint: lem-pur-system-derived-subsequence). -/
def systemDerivedSubsequenceComposition (r s : ℕ ↪o ℕ) :
    derivedSystemSubsequence B r ⋙ derivedSystemSubsequence (selectedSystemRings B r) s ≅
      derivedSystemSubsequence B (s.trans r) :=
  Functor.mapDerivedCategoryCompIso (systemSubsequence B r)
    (systemSubsequence (selectedSystemRings B r) s)

/-- The subsequence compositor has the canonical cochain representative formula.
Source: Stacks 015F (blueprint: lem-pur-system-derived-subsequence).
Proof: the ordinary composite subsequence functor is definitionally the composite-index
restriction. Cancel the exact-functor compositor against its inverse and apply its
factorization identity. -/
theorem systemDerivedSubsequenceComposition_rep (r s : ℕ ↪o ℕ)
    (K : CochainComplex (StrictRingSystem B) ℤ) :
    (systemDerivedSubsequenceComposition B r s).hom.app (DerivedCategory.Q.obj K) ≫
      (systemSubsequence B (s.trans r)).mapDerivedCategoryFactors.hom.app K =
    (derivedSystemSubsequence (selectedSystemRings B r) s).map
      ((systemSubsequence B r).mapDerivedCategoryFactors.hom.app K) ≫
    (systemSubsequence (selectedSystemRings B r) s).mapDerivedCategoryFactors.hom.app
      (((systemSubsequence B r).mapHomologicalComplex (.up ℤ)).obj K) := by
  let e := Functor.mapDerivedCategoryCompIso (systemSubsequence B r)
    (systemSubsequence (selectedSystemRings B r) s)
  apply (cancel_epi (e.inv.app (DerivedCategory.Q.obj K))).1
  change e.inv.app _ ≫ (e.hom.app _ ≫ _) = _
  erw [Iso.inv_hom_id_app_assoc]
  exact (Functor.mapDerivedCategoryCompIso_hom_app_factors
    (systemSubsequence B r) (systemSubsequence (selectedSystemRings B r) s) K).symm

end SheafOfModules
