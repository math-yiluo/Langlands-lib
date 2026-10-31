import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Interval.Set.Infinite

/-!
# Uniqueness of rational continuation in the local spectral variable

The continuation relation requires agreement away from denominator zeros on
a right half-plane. Uniqueness is proved algebraically; existence is not assumed.
-/

noncomputable section

namespace Langlands.RankinSelberg

open Polynomial

/-- Two rational functions agreeing on an infinite set away from both
denominators are equal. The scalar field and the set are arbitrary. -/
theorem rationalFunction_eq_of_infinite_eval_eq {K : Type*} [Field K]
    (R S : RatFunc K) (U : Set K) (hU : U.Infinite)
    (hR : ∀ x ∈ U, R.denom.eval x ≠ 0)
    (hS : ∀ x ∈ U, S.denom.eval x ≠ 0)
    (hRS : ∀ x ∈ U, RatFunc.eval (RingHom.id K) x R =
      RatFunc.eval (RingHom.id K) x S) : R = S := by
  have hcross : R.num * S.denom = S.num * R.denom := by
    apply Polynomial.eq_of_infinite_eval_eq
    apply hU.mono
    intro x hx
    have he : R.num.eval x / R.denom.eval x =
        S.num.eval x / S.denom.eval x := by
      simpa only [RatFunc.eval, Polynomial.eval₂_id] using hRS x hx
    simpa only [Set.mem_ofPred_eq, Polynomial.eval_mul] using
      (div_eq_div_iff (hR x hx) (hS x hx)).mp he
  calc
    R = algebraMap K[X] (RatFunc K) R.num /
        algebraMap K[X] (RatFunc K) R.denom := (RatFunc.num_div_denom R).symm
    _ = algebraMap K[X] (RatFunc K) S.num /
        algebraMap K[X] (RatFunc K) S.denom := by
      apply (div_eq_div_iff (RatFunc.algebraMap_ne_zero (RatFunc.denom_ne_zero R))
        (RatFunc.algebraMap_ne_zero (RatFunc.denom_ne_zero S))).mpr
      simpa only [← map_mul] using congrArg (algebraMap K[X] (RatFunc K)) hcross
    _ = S := RatFunc.num_div_denom S

/-- The local spectral variable, with residue cardinality `q` in applications. -/
def spectralPoint (q : ℕ) (s : ℂ) : ℂ := (q : ℂ) ^ (-s)

/-- The spectral point never vanishes for positive `q`. -/
theorem spectralPoint_ne_zero_of_pos {q : ℕ} (hq : 0 < q) (s : ℂ) : spectralPoint q s ≠ 0 := by
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  exact fun h => hq0 ((Complex.cpow_eq_zero_iff _ _).mp h).1

/-- Agreement with a rational function on an actual right half-plane.
Denominator nonvanishing is required there, so totalized evaluation at a pole
cannot supply an unintended equality. -/
def HasRationalContinuation (q : ℕ) (f : ℂ → ℂ) (R : RatFunc ℂ) : Prop :=
  ∃ a : ℝ, ∀ s : ℂ, a < s.re →
    R.denom.eval (spectralPoint q s) ≠ 0 ∧
    f s = RatFunc.eval (RingHom.id ℂ) (spectralPoint q s) R

/-- On real spectral parameters, the complex spectral point is the ordinary
positive real power, embedded in the complex numbers. -/
theorem spectralPoint_ofReal (q : ℕ) (s : ℝ) :
    spectralPoint q (s : ℂ) = ((q : ℝ) ^ (-s) : ℝ) := by
  simpa only [spectralPoint, Complex.ofReal_neg, Complex.ofReal_natCast] using
    (Complex.ofReal_cpow (Nat.cast_nonneg q) (-s)).symm

/-- The spectral point is injective on real parameters when `q > 1`. -/
theorem spectralPoint_ofReal_injective {q : ℕ} (hq : 1 < q) :
    Function.Injective (fun s : ℝ => spectralPoint q (s : ℂ)) := by
  intro s t h
  have hq' : (1 : ℝ) < q := by exact_mod_cast hq
  change spectralPoint q (s : ℂ) = spectralPoint q (t : ℂ) at h
  rw [spectralPoint_ofReal, spectralPoint_ofReal, Complex.ofReal_inj] at h
  have hn := (Real.rpow_right_inj (lt_trans zero_lt_one hq') (ne_of_gt hq')).mp h
  exact neg_injective hn

/-- Every right half-line supplies infinitely many different spectral points. -/
theorem infinite_spectralPoints_on_right {q : ℕ} (hq : 1 < q) (a : ℝ) :
    Set.Infinite ((fun s : ℝ => spectralPoint q (s : ℂ)) '' Set.Ioi a) :=
  (Set.Ioi_infinite a).image (spectralPoint_ofReal_injective hq).injOn

/-- Rational continuation of any function of the spectral parameter is unique.
This does not assert that a continuation exists. -/
theorem HasRationalContinuation.unique {q : ℕ} (hq : 1 < q) {f : ℂ → ℂ}
    {R S : RatFunc ℂ} (hR : HasRationalContinuation q f R)
    (hS : HasRationalContinuation q f S) : R = S := by
  obtain ⟨a, ha⟩ := hR
  obtain ⟨b, hb⟩ := hS
  let U : Set ℂ := (fun s : ℝ => spectralPoint q (s : ℂ)) '' Set.Ioi (max a b)
  have hU : U.Infinite := infinite_spectralPoints_on_right hq (max a b)
  apply rationalFunction_eq_of_infinite_eval_eq R S U hU
  · rintro x ⟨s, hs, rfl⟩
    exact (ha (s : ℂ) ((le_max_left a b).trans_lt hs)).1
  · rintro x ⟨s, hs, rfl⟩
    exact (hb (s : ℂ) ((le_max_right a b).trans_lt hs)).1
  · rintro x ⟨s, hs, rfl⟩
    exact (ha (s : ℂ) ((le_max_left a b).trans_lt hs)).2.symm.trans
      (hb (s : ℂ) ((le_max_right a b).trans_lt hs)).2

/-- Existence of a rational continuation already gives unique existence,
without a separate uniqueness hypothesis or any selected factor. -/
theorem existsUnique_rationalContinuation {q : ℕ} (hq : 1 < q) (f : ℂ → ℂ)
    (h : ∃ R, HasRationalContinuation q f R) :
    ∃! R, HasRationalContinuation q f R := by
  obtain ⟨R, hR⟩ := h
  exact ⟨R, hR, fun S hS => hS.unique hq hR⟩

end Langlands.RankinSelberg
