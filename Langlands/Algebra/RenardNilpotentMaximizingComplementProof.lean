import Langlands.Algebra.RenardNilpotentMaximizingComplementStatement
import Langlands.Algebra.RenardNilpotentComplementRestrictionProof
import Langlands.Algebra.RenardNilpotentDimensionTransportProof

universe u

namespace Langlands.Renard

/-- Renard C.I: an actual maximizing nilpotent tuple and its complement bound. -/
theorem nilpotentMaximizingComplement : NilpotentMaximizingComplementStatement.{u} := by
  intro V _ _ _ l
  obtain ⟨a, hcomm, hnil, hdim⟩ := nilpotentGeneratedMaxDimension_attained l V
  have hdim' : Module.finrank ℂ (NilpotentFiltration.generatedAlgebra a) =
      nilpotentGeneratedPhi l (Module.finrank ℂ V) :=
    hdim.trans (nilpotentDimensionTransport.{u, u}.2 l V)
  refine ⟨a, hcomm, hnil, hdim', Submodule.exists_isCompl _, fun W hW => ?_⟩
  rw [← hdim']
  exact (nilpotentComplementRestriction V l a hcomm hnil W hW).2

end Langlands.Renard
