import Langlands.Analysis.UniformPowerSumLowerBound
import Langlands.Global.Factors.CuspidalPairAbsoluteConvergenceProof
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.RingTheory.RamificationInertia.Basic

/-! # Divergence of a Dirichlet series of squared power traces -/

noncomputable section

set_option autoImplicit false

universe u

namespace Langlands.Global

open NumberField
open Unramified (Eigenvalues)
open CuspidalPairFunctionalEquation (residueCardinality)
open CuspidalPairAbsoluteConvergence (logExponent one_lt_residueCardinality)
open CuspidalPairEulerConvergence (residueCardinality_eq_absNorm)
open GeneralDirichlet (SummableAt)

namespace SpectralSquare

variable {F : Type u} [Field F]

/-- The coefficient at a place and positive power for the squared-trace series. -/
def coeff {n : ℕ} {S : Finset (FinitePlace F)} (A : {v : FinitePlace F // v ∉ S} → Eigenvalues n)
    (x : {v : FinitePlace F // v ∉ S} × ℕ) : ℝ :=
  ‖(A x.1).powerTrace (x.2 + 1)‖ ^ 2 / ((x.2 : ℝ) + 1)

theorem coeff_nonneg {n : ℕ} {S : Finset (FinitePlace F)}
    (A : {v : FinitePlace F // v ∉ S} → Eigenvalues n) (x : {v : FinitePlace F // v ∉ S} × ℕ) :
    0 ≤ coeff A x := by
  unfold coeff
  positivity

private def rationalPrimeIdeal (p : Nat.Primes) : Ideal ℤ := Ideal.span {(p : ℤ)}

private theorem exists_place_above [NumberField F] (p : Nat.Primes) :
    ∃ v : FinitePlace F, v.asIdeal.under ℤ = rationalPrimeIdeal p ∧
      residueCardinality v ≤ (p : ℕ) ^ Module.finrank ℚ F := by
  have hp : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp p.prop
  let q := rationalPrimeIdeal p
  have hq : q.IsPrime := (Ideal.span_singleton_prime hp.ne_zero).mpr hp
  have hq0 : q ≠ ⊥ := mt Ideal.span_singleton_eq_bot.mp hp.ne_zero
  have : q.IsMaximal := Ideal.isMaximal_of_isPrime_of_ne_bot q hq0
  obtain ⟨P, hP, hPe⟩ := q.exists_ideal_over_prime_of_isIntegral_of_isDomain (S := 𝓞 F) (by
    rw [(RingHom.injective_iff_ker_eq_bot _).mp (FaithfulSMul.algebraMap_injective ℤ _)]
    exact bot_le)
  have hP0 : P ≠ ⊥ := by
    intro he
    rw [he, Ideal.under_bot] at hPe
    exact hq0 hPe.symm
  let v : FinitePlace F := ⟨P, hP, hP0⟩
  have hOver : P.LiesOver q := ⟨hPe.symm⟩
  let Q : q.primesOver (𝓞 F) := ⟨P, hP, hOver⟩
  have hterm : P.ramificationIdx ℤ * P.inertiaDeg ℤ ≤ Module.finrank ℚ F := by
    rw [← NumberField.RingOfIntegers.rank, ← Ideal.sum_ramification_inertia_eq_finrank q (𝓞 F)]
    exact Finset.single_le_sum (f := fun Q : q.primesOver (𝓞 F) =>
      Q.1.ramificationIdx ℤ * Q.1.inertiaDeg ℤ) (fun _ _ => Nat.zero_le _) (Finset.mem_univ Q)
  have hf : P.inertiaDeg ℤ ≤ Module.finrank ℚ F :=
    (Nat.le_mul_of_pos_left _ (P.ramificationIdx_pos ℤ)).trans hterm
  refine ⟨v, hPe, ?_⟩
  have : P.LiesOver (Ideal.span {((p : ℕ) : ℤ)}) := hOver
  rw [residueCardinality_eq_absNorm, show v.asIdeal = P from rfl,
    ← Ideal.pow_inertiaDeg (p : ℕ) P]
  exact Nat.pow_le_pow_right p.prop.pos hf

end SpectralSquare

open SpectralSquare (coeff)

/-- For a positive-rank spectrum at each place outside `S`, one eigenvalue of norm at least
one at each such place suffices for divergence of the squared-trace series at
`σ = 1 / (n [F : ℚ])`. -/
def SpectralSquareDivergenceStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (S : Finset (FinitePlace F)) (n : ℕ), 0 < n →
    ∀ A : {v : FinitePlace F // v ∉ S} → Eigenvalues n,
      (∀ v, ∃ a ∈ (A v : Multiset ℂˣ), 1 ≤ ‖(a : ℂ)‖) →
      ¬ SummableAt (coeff A) logExponent (((n : ℝ) * Module.finrank ℚ F)⁻¹)

/-- Compare one coefficient over each rational prime with its reciprocal. -/
theorem spectralSquareDivergence : SpectralSquareDivergenceStatement.{u} := by
  classical
  intro F _ _ S n hn A hA hsum
  let V := {v : FinitePlace F // v ∉ S}
  let D := (n : ℝ) * (Module.finrank ℚ F : ℝ)
  let σ := D⁻¹
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hF : 0 < Module.finrank ℚ F := Module.finrank_pos
  have hDR : 0 < D := mul_pos hnR (by exact_mod_cast hF)
  obtain ⟨ε, hε, hbound⟩ := Analysis.uniformPowerSumLowerBound n hn
  have hpowers (v : V) : ∃ j : ℕ, j + 1 ≤ n ∧ ε ≤ ‖(A v).powerTrace (j + 1)‖ := by
    obtain ⟨a, ha, ha1⟩ := hA v
    obtain ⟨z, hz⟩ := Eigenvalues.ofTuple_surjective n (A v)
    rw [← hz] at ha
    change a ∈ (List.ofFn z : Multiset ℂˣ) at ha
    obtain ⟨i, rfl⟩ := (List.mem_ofFn.mp (Multiset.mem_coe.mp ha))
    obtain ⟨k, hk, hkε⟩ := hbound (fun i => (z i : ℂ))
      (ha1.trans (norm_le_pi_norm (fun i => (z i : ℂ)) i))
    obtain ⟨hk1, hkn⟩ := Finset.mem_Icc.mp hk
    refine ⟨k - 1, by omega, ?_⟩
    rw [show k - 1 + 1 = k by omega, ← hz, Eigenvalues.powerTrace_ofTuple]
    exact hkε
  choose j hj using hpowers
  choose g hg using (SpectralSquare.exists_place_above (F := F))
  have hginj : Function.Injective g := by
    intro p p' h
    have hid := (hg p).1.symm.trans ((congrArg (fun v : FinitePlace F => v.asIdeal.under ℤ) h).trans
      (hg p').1)
    exact Subtype.ext (Int.natAbs_eq_iff_associated.mpr (Ideal.span_singleton_eq_span_singleton.mp hid))
  let B : Set Nat.Primes := g ⁻¹' (S : Set (FinitePlace F))
  have hB : B.Finite := S.finite_toSet.preimage hginj.injOn
  let v (p : ↥(Bᶜ)) : V := ⟨g p.1, p.2⟩
  let e (p : ↥(Bᶜ)) : V × ℕ := (v p, j (v p))
  have hein : Function.Injective e := by
    intro p q he
    have h : g p.1 = g q.1 := congrArg (fun x : V × ℕ => (x.1 : FinitePlace F)) he
    exact Subtype.ext (hginj h)
  have hcomp (p : ↥(Bᶜ)) :
      ε ^ 2 / (n : ℝ) * (1 / (p.1 : ℝ)) ≤
        coeff A (e p) * Real.exp (-logExponent (e p) * σ) := by
    have hp : 0 < (p.1 : ℝ) := by exact_mod_cast p.1.prop.pos
    have hlogp : 0 ≤ Real.log (p.1 : ℝ) := by
      apply Real.log_nonneg
      exact_mod_cast p.1.prop.one_lt.le
    have hlogq : Real.log (residueCardinality (v p).1 : ℝ) ≤
        (Module.finrank ℚ F : ℝ) * Real.log (p.1 : ℝ) := by
      rw [← Real.log_pow]
      exact Real.log_le_log (zero_lt_one.trans (one_lt_residueCardinality _)) (by
        exact_mod_cast (hg p.1).2)
    have hk : (j (v p) : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast (hj (v p)).1
    have hexponent : logExponent (e p) ≤ D * Real.log (p.1 : ℝ) := by
      change ((j (v p) : ℝ) + 1) * Real.log (residueCardinality (v p).1 : ℝ) ≤ _
      calc
        _ ≤ ((j (v p) : ℝ) + 1) * ((Module.finrank ℚ F : ℝ) * Real.log (p.1 : ℝ)) :=
          mul_le_mul_of_nonneg_left hlogq (by positivity)
        _ ≤ (n : ℝ) * ((Module.finrank ℚ F : ℝ) * Real.log (p.1 : ℝ)) :=
          mul_le_mul_of_nonneg_right hk (mul_nonneg (by positivity) hlogp)
        _ = _ := by rw [mul_assoc]
    have habs : logExponent (e p) * σ ≤ Real.log (p.1 : ℝ) := calc
      _ ≤ (D * Real.log (p.1 : ℝ)) * σ :=
        mul_le_mul_of_nonneg_right hexponent (inv_nonneg.mpr hDR.le)
      _ = _ := by
        dsimp only [σ]
        rw [mul_right_comm, mul_inv_cancel₀ hDR.ne', one_mul]
    have hexp : 1 / (p.1 : ℝ) ≤ Real.exp (-logExponent (e p) * σ) := by
      rw [one_div, ← Real.exp_log hp, ← Real.exp_neg, neg_mul]
      exact Real.exp_le_exp.mpr (neg_le_neg habs)
    have hc : ε ^ 2 / (n : ℝ) ≤ coeff A (e p) := calc
      _ ≤ ‖(A (v p)).powerTrace (j (v p) + 1)‖ ^ 2 / (n : ℝ) :=
        div_le_div_of_nonneg_right (pow_le_pow_left₀ hε.le (hj (v p)).2 2) hnR.le
      _ ≤ _ := div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) hk
    exact mul_le_mul hc hexp (by positivity) (SpectralSquare.coeff_nonneg A (e p))
  have hsum' : Summable (fun p : ↥(Bᶜ) => ε ^ 2 / (n : ℝ) * (1 / (p.1 : ℝ))) :=
    (hsum.comp_injective hein).of_nonneg_of_le (fun _ => by positivity) hcomp
  have hscale : ε ^ 2 / (n : ℝ) ≠ 0 := (div_pos (pow_pos hε 2) hnR).ne'
  exact Nat.Primes.not_summable_one_div
    (hB.summable_compl_iff.mp ((summable_mul_left_iff hscale).mp hsum'))

end Langlands.Global
