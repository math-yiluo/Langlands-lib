import Langlands.Geometry.Analytic.BilateralRecurrenceVanishingStatement
import Mathlib.Analysis.Normed.Group.Bounded

/-! # Proof: vanishing of decaying bilateral multiplication recurrences -/

noncomputable section

open Filter Topology

universe u v

namespace Langlands.Analytic

variable (K : Type u) [NontriviallyNormedField K]
  {A : Type v} [NormedCommRing A] [NormedAlgebra K A] [CompleteSpace A]
  [IsNoetherianRing A]

include K in
/-- A bilateral orbit of multiplication by `f` tending to zero along the
cofinite filter is zero. The proof uses that the ideal of elements with
decaying forward `f`-orbit is closed, and the uniform boundedness principle
for multiplication by the powers of `f` on it. Nilpotent elements are
allowed. -/
theorem bilateral_recurrence_eq_zero (f : A) (c : ℤ → A)
    (hc : Tendsto c cofinite (𝓝 0))
    (hrec : ∀ k : ℤ, c (k - 1) = f * c k) : ∀ k : ℤ, c k = 0 := by
  let I : Ideal A :=
    { carrier := {a | Tendsto (fun n : ℕ => f ^ n * a) atTop (𝓝 0)}
      zero_mem' := by
        change Tendsto (fun n : ℕ => f ^ n * 0) atTop (𝓝 0)
        simp
      add_mem' := by
        intro a b ha hb
        change Tendsto (fun n : ℕ => f ^ n * (a + b)) atTop (𝓝 0)
        simpa only [mul_add, add_zero] using ha.add hb
      smul_mem' := by
        intro r a ha
        change Tendsto (fun n : ℕ => f ^ n * (r * a)) atTop (𝓝 0)
        simpa only [mul_left_comm, mul_zero] using ha.const_mul r }
  have hI : IsClosed (I : Set A) := isClosed_ideal_of_noetherian_banach (K := K) I
  have : CompleteSpace I := hI.completeSpace_coe
  let T (n : ℕ) : I →L[K] A :=
    { toFun := fun a => f ^ n * (a : A)
      map_add' := by intro a b; exact mul_add _ _ _
      map_smul' := by
        intro r a
        change f ^ n * (r • (a : A)) = r • (f ^ n * (a : A))
        exact mul_smul_comm _ _ _
      cont := continuous_const.mul continuous_subtype_val }
  have hpoint : ∀ a : I, ∃ C : ℝ, ∀ n : ℕ, ‖T n a‖ ≤ C := by
    intro a
    obtain ⟨C, hC⟩ := (Metric.isBounded_range_of_tendsto _ a.property).exists_norm_le
    exact ⟨C, fun n => hC _ ⟨n, rfl⟩⟩
  obtain ⟨C, hC⟩ := banach_steinhaus hpoint
  have hpow : ∀ (n : ℕ) (k : ℤ), f ^ n * c k = c (k - (n : ℤ)) := by
    intro n
    induction n with
    | zero => intro k; simp
    | succ n ih =>
      intro k
      calc
        f ^ (n + 1) * c k = f ^ n * (f * c k) := by rw [pow_succ, mul_assoc]
        _ = f ^ n * c (k - 1) := by rw [hrec]
        _ = c (k - 1 - (n : ℤ)) := ih _
        _ = c (k - ((n + 1 : ℕ) : ℤ)) := by congr 1; omega
  have hmem : ∀ k : ℤ, c k ∈ I := by
    intro k
    have hi : Function.Injective (fun n : ℕ => k - (n : ℤ)) := by
      intro n m h
      exact_mod_cast (sub_right_inj.mp h)
    have ht : Tendsto (fun n : ℕ => k - (n : ℤ)) atTop cofinite := by
      simpa only [Nat.cofinite_eq_atTop] using hi.tendsto_cofinite
    change Tendsto (fun n : ℕ => f ^ n * c k) atTop (𝓝 0)
    simpa only [Function.comp_def, hpow] using hc.comp ht
  intro k
  have hi : Function.Injective (fun n : ℕ => k + (n : ℤ)) := by
    intro n m h
    exact_mod_cast (add_left_cancel h)
  have ht : Tendsto (fun n : ℕ => k + (n : ℤ)) atTop cofinite := by
    simpa only [Nat.cofinite_eq_atTop] using hi.tendsto_cofinite
  have hlim : Tendsto (fun n : ℕ => C * ‖c (k + (n : ℤ))‖) atTop (𝓝 0) := by
    simpa using (hc.comp ht).norm.const_mul C
  have hbound : ∀ n : ℕ, ‖c k‖ ≤ C * ‖c (k + (n : ℤ))‖ := by
    intro n
    let a : I := ⟨c (k + (n : ℤ)), hmem _⟩
    have ha : T n a = c k := by
      change f ^ n * c (k + (n : ℤ)) = c k
      simpa using hpow n (k + (n : ℤ))
    calc
      ‖c k‖ = ‖T n a‖ := congrArg norm ha.symm
      _ ≤ ‖T n‖ * ‖a‖ := (T n).le_opNorm a
      _ ≤ C * ‖c (k + (n : ℤ))‖ := mul_le_mul_of_nonneg_right (hC n) (norm_nonneg a)
  exact norm_eq_zero.mp (le_antisymm (ge_of_tendsto hlim (Eventually.of_forall hbound))
    (norm_nonneg _))

/-- Vanishing of decaying bilateral multiplication recurrences in Noetherian
Banach algebras, at the exact published, internally quantified target. -/
theorem bilateral_recurrence_vanishing :
    BilateralRecurrenceVanishingStatement.{u, v} := by
  intro K _ A _ _ _ _ f c hc hrec
  exact bilateral_recurrence_eq_zero K f c hc hrec

end Langlands.Analytic
