import Langlands.GroupScheme.AffineHomImageHopfReduction
import Langlands.AnthropicFLT.Theorems.Thm_HopfAlgebra_faithfullyFlat_subalgebra_of_comul_mem_span_of_antipode_mem

/-! # Actual fppf image factorization for affine algebraic group homomorphisms -/

noncomputable section

universe u

namespace Langlands.GroupScheme

/-- Every homomorphism between affine algebraic group schemes factors through
its actual schematic image as an fppf quotient by its full kernel followed
by a closed subgroup inclusion, at arbitrary universe and over every field. -/
theorem affineHomImage : AffineHomImageStatement.{u} := by
  apply affineHomImage_of_hopfSubalgebraFaithfullyFlat
  intro k _ H _ _ _ K hΔ hS
  exact HopfAlgebra.faithfullyFlat_subalgebra_of_comul_mem_span_of_antipode_mem K hΔ hS

end Langlands.GroupScheme
