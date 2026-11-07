import Mathlib.Algebra.Central.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-! Field-embedding conjugacy in a finite-dimensional central division algebra. -/

namespace Langlands.CentralDivision

universe uK uL uD

/-- Any two embeddings of a finite field extension into a central division algebra
are conjugate by an actual unit of that division algebra. -/
def FieldEmbeddingsConjugateStatement : Prop :=
  ∀ (K : Type uK) [Field K]
    (D : Type uD) [DivisionRing D] [Algebra K D] [FiniteDimensional K D]
    [Algebra.IsCentral K D]
    (L : Type uL) [Field L] [Algebra K L] [FiniteDimensional K L]
    (f g : L →ₐ[K] D),
    ∃ u : Dˣ, ∀ a : L, f a = (u : D) * g a * ((u⁻¹ : Dˣ) : D)

end Langlands.CentralDivision
