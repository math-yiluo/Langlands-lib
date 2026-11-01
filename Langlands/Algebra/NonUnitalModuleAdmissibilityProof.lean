import Langlands.Algebra.NonUnitalModuleAdmissibilitySimplicityProof
import Langlands.Algebra.NonUnitalModuleDualFixedPartProof

/-! Admissibility consequences in Renard I.5.1. -/

set_option autoImplicit false

noncomputable section

namespace Langlands.Algebra.NonUnitalModuleAdmissibilityProof

open MulOpposite NonUnitalModuleDual NonUnitalModuleAdmissible
open NonUnitalModuleDualFixedPartMaps NonUnitalModuleAdmissibilityStatements
open NonUnitalModuleCorner (FixedPart)

universe uA uM

variable {A : Type uA} [NonUnitalRing A] [Module ℂ A]
  [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]
  {M : Type uM} [AddCommGroup M] [NonUnitalModule A M]
  (hA : IsIdempotented A) (hM : IsNondegenerate A M)

/-- The actual nondegenerate dual of an admissible original module is admissible. -/
theorem admissibleDual : AdmissibleDual hA hM := by
  let _ := dualAction hA hM
  intro h d
  obtain ⟨e, rfl⟩ : ∃ e : Idempotent A, oppositeIdempotent e = d := by
    refine ⟨⟨d.val.unop, ?_⟩, Idempotent.ext rfl⟩
    change d.val.unop * d.val.unop = d.val.unop
    exact congrArg unop d.property.eq
  change @FiniteDimensional ℂ (RightFixedPart hA hM e) _ _
    (NonUnitalModuleCorner.complexModule hA.op (isNondegenerate hA hM)
      (oppositeIdempotent e))
  rw [← rightFixedModule_eq_canonical hA hM e]
  let _ := rightFixedModule hA hM e
  let _ := NonUnitalModuleCorner.complexModule hA hM e
  let _ := h e
  obtain ⟨E, _, _⟩ :=
    (NonUnitalModuleDualFixedPart.fixedPartDuality.{uA, uM, uM} hA hM e).2.1
  exact FiniteDimensional.of_injective E.toLinearMap E.injective

/-- The proposition and both actual-dual consequences of Renard I.5.1. -/
theorem admissibilityDuality : AdmissibilityDuality.{uA, uM} := by
  intro A _ _ _ _ M _ _ hA hM
  exact
    ⟨NonUnitalModuleAdmissibilityReflexivityProof.admissibleIffEvaluationBijective hA hM,
      admissibleDual hA hM,
      NonUnitalModuleAdmissibilitySimplicityProof.admissibleSimpleIffDualSimple hA hM⟩

example : AdmissibilityDuality.{uA, uM} := admissibilityDuality.{uA, uM}
example : AdmissibilityDuality.{0, 1} := admissibilityDuality.{0, 1}
example : AdmissibilityDuality.{1, 0} := admissibilityDuality.{1, 0}

end Langlands.Algebra.NonUnitalModuleAdmissibilityProof
