import Langlands.Algebra.NonUnitalModuleFixedBidualMaps

/-!
# Fixed-bidual comparison and its canonical evaluation compatibility

Internal steps in the corrected Renard I.5.1 reflexivity argument,
printed p.26 / PDF32 of the 9 July 2026 edition.
-/

set_option autoImplicit false

namespace Langlands.Algebra.NonUnitalModuleFixedBidualStatements

open NonUnitalModuleDual NonUnitalModuleFixedBidualMaps
open NonUnitalModuleCorner (FixedPart)

universe uA uM

section Individual

variable {A : Type uA} [NonUnitalRing A] [Module ℂ A]
  [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]
  {M : Type uM} [AddCommGroup M] [NonUnitalModule A M]
  (hA : IsIdempotented A) (hM : IsNondegenerate A M)

/-- The two concrete maps are inverse, without a finiteness hypothesis. -/
def InverseComparisons : Prop :=
  ∀ e : Idempotent A,
    Function.LeftInverse (fromOrdinaryBidual hA hM e) (toOrdinaryBidual hA hM e) ∧
      Function.RightInverse (fromOrdinaryBidual hA hM e) (toOrdinaryBidual hA hM e)

/-- The inverse comparison sends ordinary evaluation to the actual evaluation. -/
def EvaluationCompatibility : Prop :=
  ∀ e : Idempotent A,
    letI := NonUnitalModuleCorner.complexModule hA hM e
    ∀ x : FixedPart e M,
      (fromOrdinaryBidual hA hM e (Module.Dual.eval ℂ (FixedPart e M) x)).val =
        evaluation hA hM x.val

end Individual

/-- Both internal comparisons, retaining every original algebra and action parameter. -/
def FixedBidualComparisons : Prop :=
  ∀ (A : Type uA) [NonUnitalRing A] [Module ℂ A]
    [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]
    (M : Type uM) [AddCommGroup M] [NonUnitalModule A M]
    (hA : IsIdempotented A) (hM : IsNondegenerate A M),
    InverseComparisons hA hM ∧ EvaluationCompatibility hA hM

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {M : Type uM} → [AddCommGroup M] → [NonUnitalModule A M] →
    IsIdempotented A → IsNondegenerate A M → Prop :=
  @InverseComparisons.{uA, uM}

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {M : Type uM} → [AddCommGroup M] → [NonUnitalModule A M] →
    IsIdempotented A → IsNondegenerate A M → Prop :=
  @EvaluationCompatibility.{uA, uM}

example : Prop := FixedBidualComparisons.{uA, uM}

end Langlands.Algebra.NonUnitalModuleFixedBidualStatements
