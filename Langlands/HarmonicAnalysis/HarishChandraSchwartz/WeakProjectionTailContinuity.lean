import Langlands.HarmonicAnalysis.HarishChandraSchwartz.UniformExponentAnnihilators

/-! # Continuity of the weak projection from a tail of translates -/

noncomputable section

open Polynomial Langlands.HarmonicAnalysis

namespace Langlands.HarishChandraSchwartz

private theorem aeval_mul_sub_eq_zero {V : Type*} [AddCommGroup V] [Module ℂ V]
    (T : Module.End ℂ V) {p q : ℂ[X]} {v w : V}
    (hv : aeval T p v = 0) (hw : aeval T q w = 0) :
    aeval T (p * q) (v - w) = 0 := by
  rw [map_sub]
  have h₁ : aeval T (p * q) v = 0 := by
    rw [mul_comm p q, map_mul, Module.End.mul_apply, hv, map_zero]
  rw [h₁, map_mul, Module.End.mul_apply, hw, map_zero, sub_zero]

variable {κ M A : Type*} [TopologicalSpace κ] [Group M] [CommGroup A]
  {j : A →* M} {a : A} {F : κ → M → ℂ}

/-- If the weak and positive parts have uniform split annihilators, continuity of all
sufficiently deep translates of the full functions implies continuity of the weak part. -/
def UniformWeakProjectionTailContinuityStatement : Prop :=
  ∀ (j : A →* M) (a : A) (F : κ → M → ℂ),
    HasUniformSplitAnnihilators j a F → ∀ (m : M) (N : ℕ),
      (∀ n, N ≤ n → Continuous (fun ω => F ω (m * j a ^ n))) →
      Continuous (fun ω => weakPart j (F ω) m)

/-- A bounded projecting polynomial divisible by `X ^ N` uses only the prescribed tail. -/
theorem HasUniformSplitAnnihilators.continuous_weakPart_of_tail
    (h : HasUniformSplitAnnihilators j a F) (m : M) (N : ℕ)
    (hTail : ∀ n, N ≤ n → Continuous (fun ω => F ω (m * j a ^ n))) :
    Continuous (fun ω => weakPart j (F ω) m) := by
  classical
  obtain ⟨Nw, Np, θ, pw, pp, hθ₀, hθ, hpw, hpp, hNw, hNp, hrw, hrp, hw, hp⟩ := h
  rw [continuous_iff_continuousAt]
  intro ω₀
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  let D := Np + Np + N
  let K := D * (Nw + Nw - 1) + D + 1
  let s := (Finset.range K).filter (fun n => N ≤ n)
  obtain ⟨C, hC⟩ := exists_projection_polynomial (Nw + Nw) D hθ
  let sample (n : ℕ) (ω : κ) := F ω (m * j a ^ n) - F ω₀ (m * j a ^ n)
  have hcont : Continuous (fun ω => |C| * ∑ n ∈ s, ‖sample n ω‖) :=
    continuous_const.mul (continuous_finsetSum s fun n hn =>
      ((hTail n (Finset.mem_filter.mp hn).2).sub continuous_const).norm)
  refine squeeze_zero (g := fun ω => |C| * ∑ n ∈ s, ‖sample n ω‖)
    (fun ω => norm_nonneg _) (fun ω => ?_) ?_
  · let W := pw ω * pw ω₀
    let P := (pp ω * pp ω₀) * X ^ N
    have hW : W.Monic := (hpw ω).mul (hpw ω₀)
    have hP : P.Monic := ((hpp ω).mul (hpp ω₀)).mul (monic_X_pow N)
    have hdW : W.natDegree = Nw + Nw := by
      simp only [W, (hpw ω).natDegree_mul (hpw ω₀), hNw]
    have hdP : P.natDegree = D := by
      simp only [P, ((hpp ω).mul (hpp ω₀)).natDegree_mul (monic_X_pow N),
        (hpp ω).natDegree_mul (hpp ω₀), natDegree_X_pow, hNp, D]
    have hrootW : ∀ z ∈ W.roots, ‖z‖ = 1 := by
      intro z hz
      change z ∈ (pw ω * pw ω₀).roots at hz
      rw [roots_mul hW.ne_zero, Multiset.mem_add] at hz
      exact hz.elim (hrw ω z) (hrw ω₀ z)
    have hrootP : ∀ z ∈ P.roots, ‖z‖ ≤ θ := by
      intro z hz
      change z ∈ ((pp ω * pp ω₀) * X ^ N).roots at hz
      rw [roots_mul hP.ne_zero, Multiset.mem_add] at hz
      rcases hz with hz | hz
      · rw [roots_mul ((hpp ω).mul (hpp ω₀)).ne_zero, Multiset.mem_add] at hz
        exact hz.elim (hrp ω z) (hrp ω₀ z)
      · have hz₀ : z ^ N = 0 := by
          simpa only [IsRoot.def, eval_pow, eval_X] using isRoot_of_mem_roots hz
        rw [eq_zero_of_pow_eq_zero hz₀, norm_zero]
        exact hθ₀
    obtain ⟨E, hE, hEW, hEP⟩ := hC W P hW hP hdW hdP hrootW hrootP
    have hX : X ^ N ∣ E := dvd_trans (dvd_mul_left _ _) hEP
    have hzero (n : ℕ) (hn : ¬ N ≤ n) : E.coeff n = 0 := by
      obtain ⟨Q, rfl⟩ := hX
      rw [coeff_X_pow_mul', ite_eq_right hn]
    let T := GroupAction.rightFunctions (j a)
    let Wdiff := weakPart j (F ω) - weakPart j (F ω₀)
    let Pdiff := positivePart j (F ω) - positivePart j (F ω₀)
    have hsplit : F ω - F ω₀ = Wdiff + Pdiff := by
      calc
        F ω - F ω₀ =
            (weakPart j (F ω) + positivePart j (F ω)) -
              (weakPart j (F ω₀) + positivePart j (F ω₀)) :=
          congrArg₂ (· - ·) (weakPart_add_positivePart j (F ω)).symm
            (weakPart_add_positivePart j (F ω₀)).symm
        _ = Wdiff + Pdiff := by
          dsimp only [Wdiff, Pdiff]
          abel
    have hWdiff : aeval T W Wdiff = 0 := aeval_mul_sub_eq_zero T (hw ω) (hw ω₀)
    have hPdiff : aeval T P Pdiff = 0 := by
      change aeval T ((pp ω * pp ω₀) * X ^ N) Pdiff = 0
      rw [mul_comm (pp ω * pp ω₀), map_mul, Module.End.mul_apply,
        aeval_mul_sub_eq_zero T (hp ω) (hp ω₀), map_zero]
    have he := congrFun (aeval_apply_eq_of_dvd T hEW hEP hsplit hWdiff hPdiff) m
    have hpow (n : ℕ) : (T ^ n) (F ω - F ω₀) m = sample n ω := by
      rw [show T = GroupAction.rightFunctions (j a) from rfl, ← map_pow,
        GroupAction.rightFunctions_apply]
      rfl
    have hdeg : E.natDegree < K := lt_of_le_of_lt hE.1 (Nat.lt_succ_self _)
    rw [aeval_eq_sum_range' hdeg, LinearMap.sum_apply, Finset.sum_apply] at he
    simp only [LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, hpow] at he
    have he' : ∑ n ∈ s, E.coeff n * sample n ω = Wdiff m := by
      rw [Finset.sum_filter]
      refine (Finset.sum_congr rfl fun n _ => ?_).trans he
      by_cases hn : N ≤ n
      · rw [ite_eq_left hn]
      · rw [ite_eq_right hn, hzero n hn, zero_mul]
    change ‖Wdiff m‖ ≤ _
    rw [← he', Finset.mul_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right ((hE.2 n).trans (le_abs_self C)) (norm_nonneg _)
  · simpa only [sample, sub_self, norm_zero, Finset.sum_const_zero, mul_zero] using hcont.tendsto ω₀

/-- The tail continuity statement holds for all families satisfying its split hypotheses. -/
theorem uniformWeakProjectionTailContinuity :
    UniformWeakProjectionTailContinuityStatement (κ := κ) (M := M) (A := A) :=
  fun _ _ _ h m N hTail => h.continuous_weakPart_of_tail m N hTail

end Langlands.HarishChandraSchwartz
