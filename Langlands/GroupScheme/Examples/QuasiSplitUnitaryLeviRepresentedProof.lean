import Langlands.GroupScheme.Examples.QuasiSplitUnitaryLeviRepresentedStatement
import Langlands.GroupScheme.Examples.QuasiSplitUnitaryLeviRange
import Langlands.GroupScheme.Examples.QuasiSplitUnitaryDynamicProof
import Langlands.GroupScheme.Examples.QuasiSplitUnitaryLeviClosed

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry Algebra
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.QuasiSplitUnitary

variable {F E : Type u} [Field F] [Field E] [Algebra F E]
  [IsQuadraticExtension F E]
variable {κ : Type u} [Fintype κ]
  (b : Module.Basis κ F (Matrix (Fin 2) (Fin 2) E)) (c : E ≃ₐ[F] E)

/-- The Weil-restricted multiplicative group represents the dynamic centralizer. -/
theorem centralizer_isRepresentedBy_leviHom :
    (Dynamic.centralizer (cocharacter b c)).IsRepresentedBy (leviHom b c) := by
  rw [centralizer_cocharacter b c]
  exact diagonal_isRepresentedBy_leviHom b c

/-- The dynamic centralizer is represented by the closed Weil-restriction Levi subgroup. -/
theorem leviRepresentedStatement : LeviRepresentedStatement.{u} := by
  intro F E _ _ _ _ κ _ b c _
  exact ⟨centralizer_isRepresentedBy_leviHom b c, isClosedSubgroup_leviHom b c⟩

end Langlands.GroupScheme.QuasiSplitUnitary
