import Langlands.Algebra.RenardNilpotentComplementRestrictionStatement
import Langlands.Algebra.RenardNilpotentComplementGenerationProof
import Langlands.Algebra.RenardNilpotentIdealFiltration
import Langlands.Algebra.CommutingDimensionHelpers

noncomputable section

open scoped Pointwise IsMulCommutative

universe u

namespace Langlands.Renard

/-- Renard C.I: restriction to a complement is injective and bounds the algebra dimension. -/
theorem nilpotentComplementRestriction : NilpotentComplementRestrictionStatement.{u} := by
  intro V _ _ _ l a hcomm hnil W hW
  let := NilpotentFiltration.generatedAlgebra_isMulCommutative a hcomm
  have hspanR := (nilpotentComplementGeneration V l a hcomm hnil W hW).2
  have hspan :
      Submodule.span ℂ
        {v : V | ∃ r : NilpotentFiltration.generatedAlgebra a,
          ∃ w : W, v = r.val w} = ⊤ := by
    have hset :
        {v : V | ∃ r : NilpotentFiltration.generatedAlgebra a,
          ∃ w : W, v = r.val w} =
        (Set.univ : Set (NilpotentFiltration.generatedAlgebra a)) • (W : Set V) := by
      ext v
      constructor
      · rintro ⟨r, w, rfl⟩
        exact ⟨r, Set.mem_univ _, w, w.property, rfl⟩
      · rintro ⟨r, _, w, hw, rfl⟩
        exact ⟨r, ⟨w, hw⟩, rfl⟩
    rw [hset, Submodule.span_smul_of_span_eq_top (Submodule.span_univ (R := ℂ))]
    change (Submodule.span (NilpotentFiltration.generatedAlgebra a)
      (W : Set V)).restrictScalars ℂ = ⊤
    rw [hspanR, Submodule.restrictScalars_top]
  have hcommR :
      ∀ r s : NilpotentFiltration.generatedAlgebra a,
        Commute (r : Module.End ℂ V) (s : Module.End ℂ V) := by
    intro r s
    exact congrArg Subtype.val (mul_comm r s)
  exact ⟨Langlands.CommutingDimension.restriction_injective ℂ V
      (NilpotentFiltration.generatedAlgebra a) hcommR W hspan,
    Langlands.CommutingDimension.dimension_le_generating_subspace ℂ V
      (NilpotentFiltration.generatedAlgebra a) hcommR W hspan⟩

end Langlands.Renard
