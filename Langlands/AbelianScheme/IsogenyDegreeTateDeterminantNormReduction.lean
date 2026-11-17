import Langlands.AbelianScheme.IsogenyDegreeTateDeterminantNormStatement
import Langlands.AbelianScheme.IsogenyFinrankKernelCardStatement
import Langlands.AbelianScheme.IsogenyKernelCardTateDeterminantStatement
import Langlands.AbelianScheme.TateDeterminantNonzeroSurjectiveStatement
import Langlands.AbelianScheme.FieldSurjectiveEndomorphismIsogenyStatement

/-! # The `p`-adic degree comparison from four inputs -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme

/-- The four inputs imply `IsogenyDegreeTateDeterminantNormStatement`, at the same
universe. -/
def IsogenyDegreeTateDeterminantNormReductionStatement : Prop :=
  IsogenyFinrankKernelCardStatement.{u} →
    IsogenyKernelCardTateDeterminantStatement.{u} →
      TateDeterminantNonzeroSurjectiveStatement.{u} →
        FieldSurjectiveEndomorphismIsogenyStatement.{u} →
          IsogenyDegreeTateDeterminantNormStatement.{u}

/-- Proof of the reduction. -/
theorem isogenyDegreeTateDeterminantNormReduction :
    IsogenyDegreeTateDeterminantNormReductionStatement.{u} := by
  intro hcard hnorm hsurj hiso k _ _ _ A p _ α
  have hp : (p : k) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  refine ⟨fun hα y => ?_, fun hα => ?_⟩
  · rw [hcard k A A α hα y]
    exact hnorm k A p hp α hα
  · by_contra hdet
    exact hα (hiso k A α (hsurj k A p α hdet))

end Langlands.AbelianScheme
