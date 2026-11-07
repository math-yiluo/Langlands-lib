import Langlands.GroupScheme.Rational.ClassFunctions
import Langlands.GroupScheme.MatrixRepresentation.AffineCoefficients
import Mathlib.LinearAlgebra.Matrix.Trace

/-! # Trace characters in the actual invariant coordinate algebra -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme.MatrixRepresentation

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    {n : Type} [Fintype n] [DecidableEq n]
    (ρ : MatrixRepresentation G n)

/-- The trace of the universal matrix as an actual regular coordinate. -/
def traceCoordinate : ClassFunctions.Coord G :=
  Matrix.trace ρ.universalCharacterMatrix

/-- The trace coordinate evaluates to the trace of the given representation. -/
theorem traceCoordinate_evaluate {A : Type u} [CommRing A] [Algebra k A]
    (g : Lie.AffinePoints G A) :
    Lie.pointCoordinates G g (traceCoordinate ρ) =
      Matrix.trace (ρ.affineMatrix (CommAlgCat.of (CommRingCat.of k) A) g :
        Matrix n n A) := by
  unfold traceCoordinate
  rw [AddMonoidHom.map_trace]
  exact congrArg Matrix.trace (AffineCoefficients.universalCharacterMatrix_map ρ
    (CommAlgCat.of (CommRingCat.of k) A) g)

/-- Trace is invariant under conjugation on every affine coefficient algebra. -/
theorem traceCoordinate_mem :
    traceCoordinate ρ ∈ ClassFunctions.algebra G := by
  apply (ClassFunctions.mem_algebra_iff_invariant G).mpr
  intro A _ _ g z
  rw [traceCoordinate_evaluate, traceCoordinate_evaluate]
  simp only [map_mul, map_inv, Units.val_mul]
  exact Matrix.trace_units_conj _ _

/-- The trace character as an element of the actual invariant subalgebra. -/
def traceClassFunction : ClassFunctions.algebra G :=
  ⟨traceCoordinate ρ, traceCoordinate_mem ρ⟩

@[simp] theorem traceClassFunction_val :
    (traceClassFunction ρ).val = traceCoordinate ρ := rfl

/-- Evaluation of the actual class function is the ordinary matrix trace. -/
theorem traceClassFunction_evaluate {A : Type u} [CommRing A] [Algebra k A]
    (g : Lie.AffinePoints G A) :
    Lie.pointCoordinates G g (traceClassFunction ρ).val =
      Matrix.trace (ρ.affineMatrix (CommAlgCat.of (CommRingCat.of k) A) g :
        Matrix n n A) :=
  traceCoordinate_evaluate ρ g

end Langlands.GroupScheme.MatrixRepresentation
