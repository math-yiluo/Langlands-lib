import Langlands.AbelianScheme.Rational
import Langlands.AbelianScheme.Tate.RationalPrimeHom
import Mathlib.LinearAlgebra.Trace

/-! # The geometric endomorphism trace through the actual prime Tate action -/

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace Langlands.AbelianScheme

variable {k : Type u} [Field k]
  (A : AbelianScheme (Scheme.Spec.obj (Opposite.op (CommRingCat.of k))))

/-- Trace of the actual rational endomorphism action on the actual prime Tate module.
Finite dimension and rationality are conclusions of the separate comparison target. -/
def primeEndomorphismTrace (p : ℕ) [Fact p.Prime] : End0 A →ₗ[ℚ] ℚ_[p] :=
  ((LinearMap.trace ℚ_[p]
    (Tate.PrimeAdic.Rational A (Over.mk (𝟙 _)) p)).restrictScalars ℚ).comp
      (Tate.PrimeAdic.rationalEndAction (Over.mk (𝟙 _)) p A).toLinearMap

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- The unique rational linear lift of the actual 2-adic Tate trace, when it exists.
The zero fallback makes the construction total; the comparison target establishes
existence and agreement with every prime Tate trace on geometric characteristic-zero bases. -/
def geometricEndomorphismTrace : End0 A →ₗ[ℚ] ℚ := by
  classical
  exact if h : ∃ T : End0 A →ₗ[ℚ] ℚ,
      ∀ a, algebraMap ℚ ℚ_[2] (T a) = primeEndomorphismTrace A 2 a then
    h.choose
  else 0

/-- A rational lift, if present, determines the chosen trace uniquely. -/
theorem geometricEndomorphismTrace_eq (T : End0 A →ₗ[ℚ] ℚ)
    (hT : ∀ a, algebraMap ℚ ℚ_[2] (T a) = primeEndomorphismTrace A 2 a) :
    geometricEndomorphismTrace A = T := by
  have h : ∃ T : End0 A →ₗ[ℚ] ℚ,
      ∀ a, algebraMap ℚ ℚ_[2] (T a) = primeEndomorphismTrace A 2 a := ⟨T, hT⟩
  rw [geometricEndomorphismTrace, dite_eq_left h]
  apply LinearMap.ext
  intro a
  apply (algebraMap ℚ ℚ_[2]).injective
  exact (h.choose_spec a).trans (hT a).symm

/-- A faithful unital action of a nontrivial ring forces the actual rational
identity to be nonzero, including for the Harris--Taylor action. -/
theorem id0_ne_zero_of_faithful {S : Scheme.{u}} {B : AbelianScheme S}
    {R : Type*} [Ring R] [Nontrivial R] (i : R →+* End0 B)
    (hi : Function.Injective i) : id0 B ≠ 0 := by
  intro h
  change (1 : End0 B) = 0 at h
  have h' : i 1 = i 0 := by simpa only [map_one, map_zero] using h
  exact one_ne_zero (hi h')

end Langlands.AbelianScheme
