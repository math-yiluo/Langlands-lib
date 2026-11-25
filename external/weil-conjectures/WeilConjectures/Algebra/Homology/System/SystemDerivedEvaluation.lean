/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.System.SystemLevelLeftExtensionBasic
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-! # Componentwise cohomology and detection for strict systems

Source: Zheng, Construction 4.1; Stacks 015F and 05RU.
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

/-- Cohomology of strict systems is evaluated componentwise.
Source: Stacks 015F (blueprint: lem-pur-system-derived-evaluation). -/
def systemDerivedCohomology (n : ℕ) (q : ℤ) :
    DerivedCategory.homologyFunctor (StrictRingSystem B) q ⋙ systemEvaluation B n ≅
      derivedSystemEvaluation B n ⋙ DerivedCategory.homologyFunctor (systemLevel B n) q :=
  (systemEvaluation B n).mapDerivedCategoryHomologyFunctorIso q

/-- Cohomology vanishes exactly when it vanishes at every coefficient level.
Source: Zheng 4.1 (blueprint: lem-pur-system-derived-evaluation).
Proof: commute exact evaluation with cohomology and apply joint detection of zero
objects in the strict abelian category. -/
theorem systemDerivedHomology_isZero_iff (M : DerivedCategory (StrictRingSystem B)) (q : ℤ) :
    IsZero ((DerivedCategory.homologyFunctor (StrictRingSystem B) q).obj M) ↔
      ∀ n, IsZero ((DerivedCategory.homologyFunctor (systemLevel B n) q).obj
        ((derivedSystemEvaluation B n).obj M)) := by
  rw [strictRingSystem_isZero_iff]
  exact forall_congr' (fun n ↦ ((systemDerivedCohomology B n q).app M).isZero_iff)

/-- Derived evaluations jointly detect isomorphisms.
Source: Zheng 4.1 (blueprint: lem-pur-system-derived-evaluation).
Proof: isomorphisms in a derived category are detected by all cohomology functors.
Exact evaluation commutes with cohomology; the strict evaluations jointly detect
isomorphisms of the resulting systems. The forward direction is functoriality. -/
theorem systemDerivedEvaluation_isIso_iff
    {M N : DerivedCategory (StrictRingSystem B)} (f : M ⟶ N) :
    IsIso f ↔ ∀ n, IsIso ((derivedSystemEvaluation B n).map f) := by
  constructor
  · intro hf n
    infer_instance
  · intro h
    rw [DerivedCategory.isIso_iff]
    intro q
    apply (strictRingSystem_isIso_iff B _).2
    intro n
    have := h n
    have hi : IsIso ((DerivedCategory.homologyFunctor (systemLevel B n) q).map
        ((derivedSystemEvaluation B n).map f)) := inferInstance
    exact (NatIso.isIso_map_iff (systemDerivedCohomology B n q) f).2 hi

/-- A common cohomological bound is detected level by level.
Source: Zheng 4.1 (blueprint: lem-pur-system-derived-evaluation).
Proof: both bounds are equivalent to vanishing of cohomology in the corresponding
half-line. Interchange the level and degree quantifiers and use componentwise
cohomology and joint detection of zero objects. The same bound is used at every level. -/
theorem systemDerivedEvaluation_bounds_iff
    (M : DerivedCategory (StrictRingSystem B)) (q : ℤ) :
    (M.IsGE q ↔ ∀ n, ((derivedSystemEvaluation B n).obj M).IsGE q) ∧
      (M.IsLE q ↔ ∀ n, ((derivedSystemEvaluation B n).obj M).IsLE q) := by
  constructor
  · constructor
    · intro h n
      rw [DerivedCategory.isGE_iff]
      intro i hi
      exact (systemDerivedHomology_isZero_iff B M i).1
        ((DerivedCategory.isGE_iff M q).1 h i hi) n
    · intro h
      rw [DerivedCategory.isGE_iff]
      intro i hi
      apply (systemDerivedHomology_isZero_iff B M i).2
      intro n
      exact (DerivedCategory.isGE_iff _ q).1 (h n) i hi
  · constructor
    · intro h n
      rw [DerivedCategory.isLE_iff]
      intro i hi
      exact (systemDerivedHomology_isZero_iff B M i).1
        ((DerivedCategory.isLE_iff M q).1 h i hi) n
    · intro h
      rw [DerivedCategory.isLE_iff]
      intro i hi
      apply (systemDerivedHomology_isZero_iff B M i).2
      intro n
      exact (DerivedCategory.isLE_iff _ q).1 (h n) i hi

/-- A strict cochain map is a quasi-isomorphism exactly when every evaluation is.
Source: Zheng 4.1 (blueprint: lem-pur-system-derived-evaluation).
Proof: localization detects quasi-isomorphisms. Commute it with evaluation and use
joint detection of isomorphisms by derived evaluations. -/
theorem strictRingSystem_quasiIso_iff {K L : CochainComplex (StrictRingSystem B) ℤ}
    (f : K ⟶ L) : QuasiIso f ↔ ∀ n,
      QuasiIso (((systemEvaluation B n).mapHomologicalComplex (.up ℤ)).map f) := by
  rw [← DerivedCategory.isIso_Q_map_iff_quasiIso, systemDerivedEvaluation_isIso_iff]
  apply forall_congr'
  intro n
  rw [← DerivedCategory.isIso_Q_map_iff_quasiIso]
  exact NatIso.isIso_map_iff (systemEvaluation B n).mapDerivedCategoryFactors f

end SheafOfModules
