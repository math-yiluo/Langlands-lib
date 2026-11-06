import Mathlib.Algebra.Central.Basic
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.RingTheory.SimpleRing.Basic
import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Central simple algebras split over a separable closure

This proposition is the separably closed splitting input to finite Galois
descent. It makes no hypothesis about simplicity after scalar extension.
-/

universe u

namespace Langlands.CentralSimple

open scoped TensorProduct

/-- Every finite-dimensional central simple algebra becomes a nonzero full
matrix algebra over the separable closure of its base field. -/
def SeparableClosureSplittingStatement : Prop :=
  ∀ (K : Type u) [Field K] (A : Type u) [Ring A] [Algebra K A]
    [FiniteDimensional K A] [Algebra.IsCentral K A] [IsSimpleRing A],
    ∃ d : ℕ, 0 < d ∧
      Nonempty (SeparableClosure K ⊗[K] A ≃ₐ[SeparableClosure K]
        Matrix (Fin d) (Fin d) (SeparableClosure K))

end Langlands.CentralSimple
