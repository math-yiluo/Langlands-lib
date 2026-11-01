import Langlands.AlgebraicGeometry.Modules.DerivedSections
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-! # Euler characteristics of actual sheaf cohomology over a field -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Modules.DerivedSections

variable {K : Type u} [Field K] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of K))

/-- Every actual cohomology vector space is finite dimensional, and all
sufficiently high cohomology objects are zero. -/
def HasFiniteCohomology (M : X.Modules) : Prop :=
  (∀ n : ℕ, Module.Finite K ((relativeCohomology f n).obj M)) ∧
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → IsZero ((relativeCohomology f n).obj M)

/-- The alternating sum of dimensions of the actual derived cohomology
objects. Its domain explicitly requires cohomological finiteness. -/
def eulerCharacteristic (M : X.Modules) (_h : HasFiniteCohomology f M) : ℤ :=
  ∑ᶠ n : ℕ, (-1 : ℤ) ^ n *
    (Module.finrank K ((relativeCohomology f n).obj M) : ℤ)

end Langlands.AlgebraicGeometry.Modules.DerivedSections
