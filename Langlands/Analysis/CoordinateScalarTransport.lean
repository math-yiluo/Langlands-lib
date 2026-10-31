import Langlands.Analysis.CoordinateScalarDifferentialOperator
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! # Actual coordinate scalar operators under continuous linear changes of variables -/

noncomputable section
universe v w
set_option autoImplicit false

namespace Langlands.Analysis.CoordinateScalarOperator

variable {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {G : Type w} [NormedAddCommGroup G] [NormedSpace ℝ G] {d r : ℕ}

/-- Move every actual basis vector by `e` and compose every coefficient with its inverse. -/
def transport (D : CoordinateScalarOperator E d r) (e : E ≃L[ℝ] G) :
    CoordinateScalarOperator G d r where
  basis := D.basis.map e.toLinearEquiv
  coefficient k word := D.coefficient k word ∘ e.symm

@[simp]
theorem transport_basis (D : CoordinateScalarOperator E d r) (e : E ≃L[ℝ] G)
    (i : Fin d) : (D.transport e).basis i = e (D.basis i) :=
  rfl

@[simp]
theorem transport_coefficient (D : CoordinateScalarOperator E d r) (e : E ≃L[ℝ] G)
    (k : Fin (r + 1)) (word : Fin k.val → Fin d) (y : G) :
    (D.transport e).coefficient k word y = D.coefficient k word (e.symm y) :=
  rfl

/-- Coordinates for the operator's actual finite basis, valued in standard Euclidean space. -/
def euclideanCoordinates (D : CoordinateScalarOperator E d r) :
    E ≃L[ℝ] EuclideanSpace ℝ (Fin d) :=
  D.basis.equivFunL.trans (EuclideanSpace.equiv (Fin d) ℝ).symm

/-- The same ordered coefficient array and mapped basis in Euclidean coordinates. -/
def toEuclidean (D : CoordinateScalarOperator E d r) :
    CoordinateScalarOperator (EuclideanSpace ℝ (Fin d)) d r :=
  D.transport D.euclideanCoordinates

end Langlands.Analysis.CoordinateScalarOperator
