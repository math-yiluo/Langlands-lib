import Langlands.AlgebraicGeometry.Picard.RosatiPositivityStatement
import Langlands.CategoryTheory.RationalizationDenominators

/-! # Algebraic reductions for the actual geometric Rosati trace form -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme

variable {k : Type u} [Field k]
  (A : AbelianScheme (Scheme.Spec.obj (Opposite.op (CommRingCat.of k))))

/-- Cyclicity holds for the actual prime Tate trace without a dimension premise. -/
theorem primeEndomorphismTrace_mul_comm (p : ℕ) [Fact p.Prime] (a b : End0 A) :
    primeEndomorphismTrace A p (a * b) = primeEndomorphismTrace A p (b * a) := by
  change LinearMap.trace ℚ_[p] _
      ((Tate.PrimeAdic.rationalEndAction (Over.mk (𝟙 _)) p A) (a * b)) =
    LinearMap.trace ℚ_[p] _
      ((Tate.PrimeAdic.rationalEndAction (Over.mk (𝟙 _)) p A) (b * a))
  rw [map_mul (Tate.PrimeAdic.rationalEndAction (Over.mk (𝟙 _)) p A),
    map_mul (Tate.PrimeAdic.rationalEndAction (Over.mk (𝟙 _)) p A)]
  exact LinearMap.trace_mul_comm _ _ _

/-- The fixed rational trace is cyclic, including its totalization case. -/
theorem geometricEndomorphismTrace_mul_comm (a b : End0 A) :
    geometricEndomorphismTrace A (a * b) = geometricEndomorphismTrace A (b * a) := by
  classical
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases h : ∃ T : End0 A →ₗ[ℚ] ℚ,
      ∀ a, algebraMap ℚ ℚ_[2] (T a) = primeEndomorphismTrace A 2 a
  · rw [geometricEndomorphismTrace, dite_eq_left h]
    apply (algebraMap ℚ ℚ_[2]).injective
    rw [h.choose_spec, h.choose_spec]
    exact primeEndomorphismTrace_mul_comm A 2 a b
  · simp only [geometricEndomorphismTrace, dite_eq_right h, LinearMap.zero_apply]

namespace Rosati

variable (P : Prerequisites.{u}) (W : DualData A) (hadd : W.Additivity P)
  (lam : A ⟶ W.dual P) [HasRationalInverse P W lam]

/-- Strict diagonal positivity of the fixed trace form on actual nonzero
integral endomorphisms. This predicate is a geometric obligation, not a proof
of that obligation. -/
def IntegralDiagonalPositive : Prop :=
  ∀ f : A ⟶ A, f ≠ 0 →
    0 < traceForm P W hadd lam (CategoryTheory.End.of (homToHom0 f))
      (CategoryTheory.End.of (homToHom0 f))

/-- Separate rational scalars in the two arguments of the fixed form. -/
theorem traceForm_smul_smul (q r : ℚ) (a b : End0 A) :
    traceForm P W hadd lam (q • a) (r • b) =
      (q * r) * traceForm P W hadd lam a b := by
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, mul_assoc, mul_left_comm]

/-- Strict positivity on integral nonzero endomorphisms extends to rational ones
by clearing one nonzero integer denominator. -/
theorem traceForm_pos_of_integral
    (hpos : IntegralDiagonalPositive A P W hadd lam)
    (a : End0 A) (ha : a ≠ 0) :
    0 < traceForm P W hadd lam a a := by
  obtain ⟨n, hn, f, hf⟩ := Rationalization.exists_integral_multiple a.asHom
  have hnq : (n : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hn
  have hf' : (CategoryTheory.End.of (homToHom0 f) : End0 A) = (n : ℚ) • a := by
    apply CategoryTheory.End.ext
    change Rationalization.ofHom f = (n : ℚ) • a.asHom
    simpa only [Int.cast_smul_eq_zsmul] using hf
  have hf0 : f ≠ 0 := by
    intro heq
    have hz : (n : ℚ) • a = 0 := by rw [← hf', heq, map_zero] <;> rfl
    exact ha ((smul_eq_zero.mp hz).resolve_left hnq)
  have h := hpos f hf0
  rw [hf', traceForm_smul_smul] at h
  exact (mul_pos_iff_of_pos_left (mul_self_pos.mpr hnq)).mp h

/-- Trace invariance and the anti-involution equations give symmetry of the
actual trace form; these geometric equations remain explicit obligations here. -/
theorem traceForm_symm_of_trace_invariant
    (htrace : ∀ a : End0 A,
      geometricEndomorphismTrace A (involution P W hadd lam a) =
        geometricEndomorphismTrace A a)
    (hmul : ∀ a b : End0 A,
      involution P W hadd lam (a * b) =
        involution P W hadd lam b * involution P W hadd lam a)
    (hinv : ∀ a : End0 A,
      involution P W hadd lam (involution P W hadd lam a) = a)
    (a b : End0 A) :
    traceForm P W hadd lam a b = traceForm P W hadd lam b a := by
  rw [traceForm_apply, traceForm_apply, ← htrace (a * involution P W hadd lam b),
    hmul, hinv]

/-- Assemble the three clauses after the geometric trace invariance,
anti-involution equations and integral strict positivity have been established. -/
theorem positivity_at_of_integral
    (htrace : ∀ a : End0 A,
      geometricEndomorphismTrace A (involution P W hadd lam a) =
        geometricEndomorphismTrace A a)
    (hmul : ∀ a b : End0 A,
      involution P W hadd lam (a * b) =
        involution P W hadd lam b * involution P W hadd lam a)
    (hinv : ∀ a : End0 A,
      involution P W hadd lam (involution P W hadd lam a) = a)
    (hpos : IntegralDiagonalPositive A P W hadd lam) :
    (∀ a b : End0 A, traceForm P W hadd lam a b = traceForm P W hadd lam b a) ∧
      (∀ a : End0 A, 0 ≤ traceForm P W hadd lam a a) ∧
      ∀ a : End0 A, a ≠ 0 →
        0 < geometricEndomorphismTrace A (a * involution P W hadd lam a) := by
  have hstrict := traceForm_pos_of_integral A P W hadd lam hpos
  refine ⟨traceForm_symm_of_trace_invariant A P W hadd lam htrace hmul hinv, ?_, ?_⟩
  · intro a
    by_cases ha : a = 0
    · simp [ha]
    · exact (hstrict a ha).le
  · exact hstrict

end Rosati
end Langlands.AbelianScheme
