import Langlands.HarmonicAnalysis.PointwiseTestModuleUniquenessStatement

/-!
# Uniqueness of the actual smooth multiplier extension

Renard (9 July 2026), II.2.5 lemma, printed p.39 / PDF45.
-/

set_option autoImplicit false

namespace Langlands.HarmonicAnalysis.PointwiseTestModule

open Langlands.Algebra PointwiseTestAlgebra

universe uX uM

/-- Agreement on included tests forces equality with the canonical smooth module. -/
theorem smoothExtensionUnique (X : Type uX) [TopologicalSpace X] :
    SmoothExtensionUniqueStatement.{uX, uM} X := by
  intro M _ μM hM σM h
  let _ := σM
  let _ : IsScalarTower (LocallyConstant X ℂ) (Carrier X) M :=
    ⟨fun f a m => by
      calc
        (f • a) • m = inclusion (f • a) • m := (h _ _).symm
        _ = (f * inclusion a) • m := by rw [inclusion_ambient_smul]
        _ = f • (inclusion a • m) := mul_smul _ _ _
        _ = f • (a • m) := congrArg (fun n : M => f • n) (h a m)⟩
  exact (NondegenerateScalars.module_eq_of_compatible
    (LocallyConstant X ℂ) isIdempotented hM).symm

end Langlands.HarmonicAnalysis.PointwiseTestModule
