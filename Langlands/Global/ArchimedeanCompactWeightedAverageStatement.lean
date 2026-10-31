import Langlands.Global.ArchimedeanCompactTypes
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! # Weighted compact averaging in the actual derivative topology -/

noncomputable section
universe u
set_option autoImplicit false

namespace Langlands.Global.ArchimedeanGL

open MeasureTheory DerivativeSmoothFunctions

variable (K : Type u) [Field K] [NumberField K] (n : ℕ)

/-- Finite Borel integration of a continuous weighted compact orbit gives a
continuous operator on actual derivative smooth functions and belongs to the
closed complex compact-orbit span of every input. -/
def CompactWeightedAverageStatement : Prop :=
  ∀ [MeasurableSpace (standardInfiniteCompact K n)]
    [BorelSpace (standardInfiniteCompact K n)]
    (ν : Measure (standardInfiniteCompact K n)) [IsFiniteMeasure ν]
    (w : C(standardInfiniteCompact K n, ℂ)),
    ∃ A : DerivativeSmoothFunctions K n →L[ℂ] DerivativeSmoothFunctions K n,
      (∀ f x, evalCLM K n x (A f) =
        ∫ k : standardInfiniteCompact K n,
          w k * evalCLM K n (x * k.val) f ∂ν) ∧
      (∀ f, A f ∈
        (Submodule.span ℂ (Set.range fun k : standardInfiniteCompact K n =>
          compactAction K n k f)).topologicalClosure)

end Langlands.Global.ArchimedeanGL
