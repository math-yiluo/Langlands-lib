import Langlands.HarmonicAnalysis.PointwiseTestModule

/-!
# Uniqueness of smooth multipliers extending an original test action
-/

universe uX uM

namespace Langlands.HarmonicAnalysis.PointwiseTestModule

open Langlands.Algebra PointwiseTestAlgebra

/-- Renard II.2.5: an ambient smooth-function module extending the specified
original nondegenerate test action equals its canonical extension. -/
def SmoothExtensionUniqueStatement (X : Type uX) [TopologicalSpace X] : Prop :=
  ∀ (M : Type uM) [AddCommGroup M]
    [μM : NonUnitalModule (Carrier X) M]
    (hM : IsNondegenerate (Carrier X) M)
    (σM : Module (LocallyConstant X ℂ) M),
    (letI := σM
     ∀ (a : Carrier X) (m : M),
       inclusion a • m = μM.toDistribSMul.toSMul.smul a m) →
    σM = module hM

end Langlands.HarmonicAnalysis.PointwiseTestModule
