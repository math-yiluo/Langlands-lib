import Mathlib.RingTheory.Finiteness.Descent
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Dimension.Free

/-! # Finiteness forced by a finite tensor decomposition -/

noncomputable section

universe u v

open scoped TensorProduct

namespace Langlands.GroupScheme

variable {k L : Type u} [Field k] [Field L] [Algebra k L]
variable {J : Type v} [Fintype J]

/-- A finite product decomposition of the scalar extension forces the original
field extension to be finite-dimensional. -/
theorem finiteDimensional_of_tensorDecomposition
    (e : (L ⊗[k] L) ≃ₐ[L] (J → L)) : FiniteDimensional k L := by
  let : Module.Finite L (L ⊗[k] L) := Module.Finite.equiv e.symm.toLinearEquiv
  exact Module.Finite.of_finite_tensorProduct_of_faithfullyFlat L

/-- The field extension in a finite tensor decomposition is algebraic. -/
theorem isAlgebraic_of_tensorDecomposition
    (e : (L ⊗[k] L) ≃ₐ[L] (J → L)) : Algebra.IsAlgebraic k L := by
  let : FiniteDimensional k L := finiteDimensional_of_tensorDecomposition e
  infer_instance

/-- An actual finite basis of the original field extension, obtained from the
supplied tensor decomposition by faithfully flat descent of finiteness. -/
def finiteBasisOfTensorDecomposition
    (e : (L ⊗[k] L) ≃ₐ[L] (J → L)) :
    Module.Basis (Fin (Module.finrank k L)) k L := by
  let : FiniteDimensional k L := finiteDimensional_of_tensorDecomposition e
  exact Module.finBasis k L

end Langlands.GroupScheme
