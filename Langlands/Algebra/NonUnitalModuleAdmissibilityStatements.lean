import Langlands.Algebra.NonUnitalModuleAdmissible
import Langlands.Algebra.NonUnitalModuleBidualEvaluation
import Mathlib.CategoryTheory.Simple

/-!
# Admissibility and the actual nondegenerate dual

Renard (9 July 2026), I.5.1, printed p.26 / PDF32.
-/

set_option autoImplicit false

namespace Langlands.Algebra.NonUnitalModuleAdmissibilityStatements

open CategoryTheory NonUnitalModuleAdmissible

universe uA uM

section Individual

variable {A : Type uA} [NonUnitalRing A] [Module ℂ A]
  [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]
  {M : Type uM} [AddCommGroup M] [NonUnitalModule A M]
  (hA : IsIdempotented A) (hM : IsNondegenerate A M)

/-- Reflexivity refers to the canonical evaluation on the actual nondegenerate dual. -/
def AdmissibleIffEvaluationBijective : Prop :=
  IsAdmissible hA hM ↔ Function.Bijective (NonUnitalModuleDual.evaluation hA hM)

/-- The dual has its unchanged opposite-ring action and its recovered coefficients. -/
def AdmissibleDual : Prop :=
  letI := NonUnitalModuleDual.dualAction hA hM
  IsAdmissible hA hM →
    IsAdmissible hA.op (NonUnitalModuleDual.isNondegenerate hA hM)

/-- Simplicity is in the actual original nondegenerate module categories. -/
def AdmissibleSimpleIffDualSimple : Prop :=
  IsAdmissible hA hM →
    (Simple (⟨NonUnitalModuleCat.of A M, hM⟩ : NondegenerateModuleCat.{uA, uM} A) ↔
      Simple (NonUnitalModuleDual.dualObject hA
        (⟨NonUnitalModuleCat.of A M, hM⟩ : NondegenerateModuleCat.{uA, uM} A)))

end Individual

/-- The proposition and both conclusions of the corollary in I.5.1. -/
def AdmissibilityDuality : Prop :=
  ∀ (A : Type uA) [NonUnitalRing A] [Module ℂ A]
    [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]
    (M : Type uM) [AddCommGroup M] [NonUnitalModule A M]
    (hA : IsIdempotented A) (hM : IsNondegenerate A M),
    AdmissibleIffEvaluationBijective hA hM ∧
      AdmissibleDual hA hM ∧ AdmissibleSimpleIffDualSimple hA hM

/-- Complete unapplied signatures keep the algebra and module universes independent. -/
example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {M : Type uM} → [AddCommGroup M] → [NonUnitalModule A M] →
    IsIdempotented A → IsNondegenerate A M → Prop :=
  @AdmissibleIffEvaluationBijective.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {M : Type uM} → [AddCommGroup M] → [NonUnitalModule A M] →
    IsIdempotented A → IsNondegenerate A M → Prop :=
  @AdmissibleDual.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {M : Type uM} → [AddCommGroup M] → [NonUnitalModule A M] →
    IsIdempotented A → IsNondegenerate A M → Prop :=
  @AdmissibleSimpleIffDualSimple.{uA, uM}

example : Prop := AdmissibilityDuality.{uA, uM}

section ExactStructures

variable {A : Type uA} [NonUnitalRing A] [Module ℂ A]
  [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]
  {M : Type uM} [AddCommGroup M] [NonUnitalModule A M]
  (hA : IsIdempotented A) (hM : IsNondegenerate A M)

/-- The target and its original action are exactly those of canonical evaluation. -/
example :
    AdmissibleIffEvaluationBijective hA hM ↔
      (IsAdmissible hA hM ↔
        letI := NonUnitalModuleDual.bidualAction hA hM
        Function.Bijective
          (NonUnitalModuleDual.evaluation hA hM :
            NonUnitalModuleHom A M (NonUnitalModuleDual.Bidual hA hM))) := Iff.rfl

/-- Admissibility of the actual dual uses its selected action and exact recovered scalars. -/
example :
    AdmissibleDual hA hM ↔
      (IsAdmissible hA hM →
        letI := NonUnitalModuleDual.dualAction hA hM
        ∀ e : Idempotent Aᵐᵒᵖ,
          letI := NonUnitalModuleCorner.complexModule hA.op
            (NonUnitalModuleDual.isNondegenerate hA hM) e
          FiniteDimensional ℂ
            (NonUnitalModuleCorner.FixedPart e (NonUnitalModuleDual.Dual hA hM))) := Iff.rfl

/-- Both simple objects are the original module and precisely its published dual object. -/
example :
    AdmissibleSimpleIffDualSimple hA hM ↔
      (IsAdmissible hA hM →
        (Simple
          (⟨NonUnitalModuleCat.of A M, hM⟩ : NondegenerateModuleCat.{uA, uM} A) ↔
          Simple (NonUnitalModuleDual.dualObject hA
            (⟨NonUnitalModuleCat.of A M, hM⟩ :
              NondegenerateModuleCat.{uA, uM} A)))) := Iff.rfl

end ExactStructures

end Langlands.Algebra.NonUnitalModuleAdmissibilityStatements
