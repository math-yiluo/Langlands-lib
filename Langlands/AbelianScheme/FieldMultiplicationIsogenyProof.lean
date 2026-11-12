import Langlands.AbelianScheme.FieldMultiplicationIsogenyStatement
import Langlands.AbelianScheme.FieldSymmetricAmpleExistenceProof
import Langlands.AbelianScheme.FieldSymmetricMultiplicationPullbackProof
import Langlands.AbelianScheme.FieldAmpleMultiplicationKernelProof
import Langlands.AbelianScheme.FieldFiniteKernelIsogenyProof

/-! # Positive multiplication isogeny over arbitrary fields -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Positive multiplication is finite, flat and surjective on a commutative
smooth proper geometrically connected group scheme over any field. -/
theorem fieldMultiplicationIsogeny : FieldMultiplicationIsogenyStatement.{u} := by
  intro K _ G _ hSmooth hProper hConnected n hn
  obtain ⟨L, hAmple, hSymmetric⟩ :=
    fieldSymmetricAmpleExistence K G hSmooth hProper hConnected
  have hPullback :=
    fieldSymmetricMultiplicationPullback K G hSmooth hProper hConnected L hSymmetric n hn
  have hKernel :=
    fieldAmpleMultiplicationKernel K G hSmooth hProper hConnected L hAmple n hn hPullback
  exact fieldFiniteKernelIsogeny K G (multiplication G (n : ℤ))
    hSmooth hProper hConnected hKernel

end Langlands.GroupScheme
