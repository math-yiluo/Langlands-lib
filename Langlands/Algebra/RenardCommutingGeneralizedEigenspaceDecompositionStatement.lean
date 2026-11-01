import Langlands.Algebra.RenardCommutingGeneralizedEigenspaceBlocks

/-! The finite decomposition and restriction comparison for the actual joint spaces. -/

noncomputable section
open scoped BigOperators

namespace Langlands.Renard

universe u

/-- The source's actual supported joint decomposition and its dimension consequences. -/
def CommutingGeneralizedEigenspaceDecompositionStatement : Prop :=
  ∀ (V : Type u) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (l : ℕ) (a : Fin l → Module.End ℂ V)
    (hcomm : ∀ i j, Commute (a i) (a j)),
    Finite (CommutingReduction.jointBlockIndex a) ∧
    iSupIndep (CommutingReduction.jointSpace a) ∧
    (⨆ χ : CommutingReduction.jointBlockIndex a,
      CommutingReduction.jointSpace a χ.val) = ⊤ ∧
    (∀ F : Fintype (CommutingReduction.jointBlockIndex a),
      letI := F
      (∑ χ : CommutingReduction.jointBlockIndex a,
        Module.finrank ℂ (CommutingReduction.jointSpace a χ.val)) =
          Module.finrank ℂ V) ∧
    Function.Injective
      (fun r : NilpotentFiltration.generatedAlgebra a =>
        fun χ : CommutingReduction.jointBlockIndex a =>
          CommutingReduction.blockRestriction a hcomm χ.val r) ∧
    (∀ F : Fintype (CommutingReduction.jointBlockIndex a),
      letI := F
      Module.finrank ℂ (NilpotentFiltration.generatedAlgebra a) ≤
        ∑ χ : CommutingReduction.jointBlockIndex a,
          Module.finrank ℂ (CommutingReduction.blockAlgebra a hcomm χ.val))

end Langlands.Renard
