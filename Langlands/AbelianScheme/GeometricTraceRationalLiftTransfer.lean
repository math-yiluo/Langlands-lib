import Langlands.AbelianScheme.GeometricEndomorphismTrace

/-! # Transfer of the fixed rational trace from a nonzero target trace -/

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace Langlands.AbelianScheme

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

variable {k K : Type u} [Field k] [Field K]
  (A : AbelianScheme (Scheme.Spec.obj (Opposite.op (CommRingCat.of k))))
  (B : AbelianScheme (Scheme.Spec.obj (Opposite.op (CommRingCat.of K))))

/-- A nonzero value of the fixed rational trace rules out its zero fallback
and therefore establishes agreement with the actual 2-adic trace. -/
theorem geometricEndomorphismTrace_twoAdic_of_ne_zero
    (b : End0 B) (hb : geometricEndomorphismTrace B b ≠ 0) (d : End0 B) :
    algebraMap ℚ ℚ_[2] (geometricEndomorphismTrace B d) =
      primeEndomorphismTrace B 2 d := by
  classical
  by_cases h : ∃ T : End0 B →ₗ[ℚ] ℚ,
      ∀ c, algebraMap ℚ ℚ_[2] (T c) = primeEndomorphismTrace B 2 c
  · rw [geometricEndomorphismTrace_eq B h.choose h.choose_spec]
    exact h.choose_spec d
  · have hz : geometricEndomorphismTrace B b = 0 := by
      simp only [geometricEndomorphismTrace, dite_eq_right h, LinearMap.zero_apply]
    exact (hb hz).elim

/-- Compatibility of the already defined rational traces along a linear map
of actual rational endomorphism spaces. -/
def GeometricTraceCompatibleLinearMap (F : End0 A →ₗ[ℚ] End0 B) : Prop :=
  ∀ a : End0 A, geometricEndomorphismTrace B (F a) = geometricEndomorphismTrace A a

/-- Actual 2-adic trace compatibility and one nonzero target trace value
transfer the fixed rational trace without a general comparison theorem. -/
theorem geometricTraceCompatibleLinearMap_of_target_ne_zero
    (F : End0 A →ₗ[ℚ] End0 B)
    (hprime : ∀ a, primeEndomorphismTrace B 2 (F a) = primeEndomorphismTrace A 2 a)
    (b : End0 B) (hb : geometricEndomorphismTrace B b ≠ 0) :
    GeometricTraceCompatibleLinearMap A B F := by
  have htarget := geometricEndomorphismTrace_twoAdic_of_ne_zero B b hb
  have hlift : ∀ a,
      algebraMap ℚ ℚ_[2] (((geometricEndomorphismTrace B).comp F) a) =
        primeEndomorphismTrace A 2 a := by
    intro a
    exact (htarget (F a)).trans (hprime a)
  have heq := geometricEndomorphismTrace_eq A
    ((geometricEndomorphismTrace B).comp F) hlift
  intro a
  exact (congrArg (fun T : End0 A →ₗ[ℚ] ℚ => T a) heq).symm

end Langlands.AbelianScheme
