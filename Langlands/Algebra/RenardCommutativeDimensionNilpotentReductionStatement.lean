import Langlands.Algebra.RenardCommutingGeneralizedEigenspaceBlocks
import Langlands.Algebra.RenardNilpotentDimensionMaximum
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Reduction through the canonical nilpotent maxima of the actual joint blocks. -/

noncomputable section
open scoped BigOperators

namespace Langlands.Renard

universe u

/-- Actual block maximum comparisons and the conditional source power-bound reduction. -/
def CommutativeDimensionNilpotentReductionStatement : Prop :=
  ∀ (V : Type u) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (l : ℕ) (a : Fin l → Module.End ℂ V)
    (hcomm : ∀ i j, Commute (a i) (a j)),
    (∀ χ : Fin l → ℂ,
      Module.finrank ℂ (CommutingReduction.blockAlgebra a hcomm χ) ≤
        nilpotentGeneratedPhi l
          (Module.finrank ℂ (CommutingReduction.jointSpace a χ))) ∧
    (∀ F : Fintype (CommutingReduction.jointBlockIndex a),
      letI := F
      Module.finrank ℂ (NilpotentFiltration.generatedAlgebra a) ≤
        ∑ χ : CommutingReduction.jointBlockIndex a,
          nilpotentGeneratedPhi l
            (Module.finrank ℂ (CommutingReduction.jointSpace a χ.val))) ∧
    (1 ≤ l →
      let r : ℝ := 2 - Real.rpow 2 (1 - (l : ℝ))
      (∀ χ : CommutingReduction.jointBlockIndex a,
        (nilpotentGeneratedPhi l
          (Module.finrank ℂ (CommutingReduction.jointSpace a χ.val)) : ℝ) ≤
            Real.rpow
              (Module.finrank ℂ (CommutingReduction.jointSpace a χ.val) : ℝ) r) →
      (Module.finrank ℂ (NilpotentFiltration.generatedAlgebra a) : ℝ) ≤
        Real.rpow (Module.finrank ℂ V : ℝ) r)

end Langlands.Renard
