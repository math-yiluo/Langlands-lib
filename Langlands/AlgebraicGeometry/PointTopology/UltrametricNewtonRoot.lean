import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Analysis.Normed.Ring.Ultra
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Tactic.LinearCombination
import Langlands.AlgebraicGeometry.PointTopology.HenselianEtalePointProof
import Langlands.Analysis.UltrametricCompletion

/-!
# Roots near approximate roots over complete ultrametric fields

Over a complete ultrametric nontrivially normed field, a polynomial `Q` with
`‖Q(t₀)‖ ≤ ‖Q'(t₀)‖` and `M ‖Q(t₀)‖ < ‖Q'(t₀)‖²`, where `M` bounds the higher Taylor
coefficients of `Q` at `t₀`, has a root within `‖Q(t₀)‖ / ‖Q'(t₀)‖` of `t₀`. The root is
the fixed point of the frozen-derivative Newton map, a contraction of a closed ball.
-/

noncomputable section

open Polynomial Metric

namespace Langlands.AlgebraicGeometry.PointTopology

namespace UltrametricNewton

variable {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]

/-- A polynomial without terms of degree below two is quadratically small on the unit ball. -/
theorem norm_eval_le (T : L[X]) {M : ℝ} (hM0 : 0 ≤ M) (hT : ∀ k, ‖T.coeff k‖ ≤ M)
    (hlow : ∀ k < 2, T.coeff k = 0) {h : L} (hh : ‖h‖ ≤ 1) :
    ‖T.eval h‖ ≤ M * ‖h‖ ^ 2 := by
  rw [eval_eq_sum_range]
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity)
  intro k _
  rcases lt_or_ge k 2 with hk | hk
  · rw [hlow k hk, zero_mul, norm_zero]
    positivity
  · rw [norm_mul, norm_pow]
    exact mul_le_mul (hT k) (pow_le_pow_of_le_one (norm_nonneg _) hh hk) (by positivity) hM0

/-- A polynomial without constant term is linearly small on the unit ball. -/
theorem norm_eval_le_linear (S : L[X]) {M : ℝ} (hM0 : 0 ≤ M) (hS : ∀ k, ‖S.coeff k‖ ≤ M)
    (h0 : S.coeff 0 = 0) {h : L} (hh : ‖h‖ ≤ 1) :
    ‖S.eval h‖ ≤ M * ‖h‖ := by
  rw [eval_eq_sum_range]
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity)
  intro k _
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [h0, zero_mul, norm_zero]
    positivity
  · rw [norm_mul, norm_pow]
    exact mul_le_mul (hS k) (by simpa using pow_le_pow_of_le_one (norm_nonneg _) hh hk)
      (by positivity) hM0

/-- In an ultrametric field, `‖x ^ k - y ^ k‖ ≤ ‖x - y‖ ρ ^ (k - 1)` when `‖x‖, ‖y‖ ≤ ρ`. -/
theorem norm_pow_sub_pow_le {x y : L} {ρ : ℝ} (hρ : 0 ≤ ρ) (hx : ‖x‖ ≤ ρ) (hy : ‖y‖ ≤ ρ)
    (k : ℕ) : ‖x ^ k - y ^ k‖ ≤ ‖x - y‖ * ρ ^ (k - 1) := by
  rw [← (Commute.all x y).geom_sum₂_mul, norm_mul, mul_comm]
  gcongr
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity)
  intro i hi
  have hi : i < k := Finset.mem_range.mp hi
  rw [norm_mul, norm_pow, norm_pow]
  calc ‖x‖ ^ i * ‖y‖ ^ (k - 1 - i) ≤ ρ ^ i * ρ ^ (k - 1 - i) := by gcongr
    _ = ρ ^ (k - 1) := by rw [← pow_add]; congr 1; omega

/-- A polynomial without terms of degree below two is Lipschitz with small constant on small
balls. -/
theorem norm_eval_sub_eval_le (T : L[X]) {M : ℝ} (hM0 : 0 ≤ M) (hT : ∀ k, ‖T.coeff k‖ ≤ M)
    (hlow : ∀ k < 2, T.coeff k = 0) {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ 1) {h h' : L}
    (hh : ‖h‖ ≤ ρ) (hh' : ‖h'‖ ≤ ρ) :
    ‖T.eval h - T.eval h'‖ ≤ M * ρ * ‖h - h'‖ := by
  rw [eval_eq_sum_range' (n := T.natDegree + 1) (Nat.lt_succ_self _),
    eval_eq_sum_range' (n := T.natDegree + 1) (Nat.lt_succ_self _), ← Finset.sum_sub_distrib]
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity)
  intro k _
  rcases lt_or_ge k 2 with hk | hk
  · rw [hlow k hk, zero_mul, zero_mul, sub_zero, norm_zero]
    positivity
  · rw [← mul_sub, norm_mul]
    calc ‖T.coeff k‖ * ‖h ^ k - h' ^ k‖ ≤ M * (‖h - h'‖ * ρ ^ (k - 1)) :=
          mul_le_mul (hT k) (norm_pow_sub_pow_le hρ0 hh hh' k) (norm_nonneg _) hM0
      _ ≤ M * (‖h - h'‖ * ρ) := by
          gcongr
          calc ρ ^ (k - 1) ≤ ρ ^ 1 := pow_le_pow_of_le_one hρ0 hρ (by omega)
            _ = ρ := pow_one ρ
      _ = M * ρ * ‖h - h'‖ := by ring

/-- **Newton root lemma** over a complete ultrametric field. -/
theorem exists_root [CompleteSpace L] (Q : L[X]) (t₀ : L) {M : ℝ}
    (hM : ∀ k, 2 ≤ k → ‖(taylor t₀ Q).coeff k‖ ≤ M)
    (h01 : ‖Q.eval t₀‖ ≤ ‖Q.derivative.eval t₀‖)
    (hsmall : M * ‖Q.eval t₀‖ < ‖Q.derivative.eval t₀‖ ^ 2) :
    ∃ τ : L, Q.eval τ = 0 ∧ ‖τ - t₀‖ ≤ ‖Q.eval t₀‖ / ‖Q.derivative.eval t₀‖ ∧
      Q.derivative.eval τ ≠ 0 := by
  set c₀ := Q.eval t₀ with hc₀
  set c₁ := Q.derivative.eval t₀ with hc₁
  set G := taylor t₀ Q with hG
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 2 le_rfl)
  have hc₁0 : c₁ ≠ 0 := by
    intro h
    rw [h, norm_zero] at hsmall
    nlinarith [norm_nonneg c₀]
  have hn₁ : 0 < ‖c₁‖ := norm_pos_iff.mpr hc₁0
  set r := ‖c₀‖ / ‖c₁‖ with hr
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r ≤ 1 := (div_le_one hn₁).mpr h01
  set q := M * r / ‖c₁‖ with hq
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q < 1 := by
    rw [hq, hr, div_lt_one hn₁, mul_div_assoc', div_lt_iff₀ hn₁]
    nlinarith
  let T : L[X] := G - C c₀ - C c₁ * X
  have hTc : ∀ k, T.coeff k = if k < 2 then 0 else G.coeff k := by
    intro k
    simp only [T, coeff_sub, coeff_C, coeff_C_mul_X]
    rcases k with _ | _ | k
    · simp [hG, taylor_coeff_zero, hc₀]
    · simp [hG, taylor_coeff_one, hc₁]
    · simp
  have hT : ∀ k, ‖T.coeff k‖ ≤ M := by
    intro k
    rw [hTc]
    split_ifs with hk
    · rw [norm_zero]; exact hM0
    · exact hM k (not_lt.mp hk)
  have hlow : ∀ k < 2, T.coeff k = 0 := fun k hk => by rw [hTc]; simp [hk]
  have hGT : ∀ h, G.eval h = c₀ + c₁ * h + T.eval h := by
    intro h
    simp only [T, eval_sub, eval_C, eval_mul, eval_X]
    ring
  let F : L → L := fun h => -(c₀ / c₁) - T.eval h / c₁
  have hmaps : ∀ h, ‖h‖ ≤ r → ‖F h‖ ≤ r := by
    intro h hh
    have h1 : ‖-(c₀ / c₁)‖ ≤ r := by rw [norm_neg, norm_div]
    have h2 : ‖T.eval h / c₁‖ ≤ r := by
      rw [norm_div, div_le_iff₀ hn₁]
      calc ‖T.eval h‖ ≤ M * ‖h‖ ^ 2 := norm_eval_le T hM0 hT hlow (hh.trans hr1)
        _ ≤ M * r ^ 2 := by gcongr
        _ = q * r * ‖c₁‖ := by rw [hq]; field_simp
        _ ≤ 1 * r * ‖c₁‖ := by gcongr
        _ = r * ‖c₁‖ := by ring
    show ‖-(c₀ / c₁) - T.eval h / c₁‖ ≤ r
    rw [sub_eq_add_neg]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h1 ?_)
    rwa [norm_neg]
  have hlip : ∀ h h', ‖h‖ ≤ r → ‖h'‖ ≤ r → ‖F h - F h'‖ ≤ q * ‖h - h'‖ := by
    intro h h' hh hh'
    have : F h - F h' = -((T.eval h - T.eval h') / c₁) := by
      simp only [F]
      ring
    rw [this, norm_neg, norm_div, div_le_iff₀ hn₁]
    calc ‖T.eval h - T.eval h'‖ ≤ M * r * ‖h - h'‖ :=
          norm_eval_sub_eval_le T hM0 hT hlow hr0 hr1 hh hh'
      _ = q * ‖h - h'‖ * ‖c₁‖ := by rw [hq]; field_simp
  let s : Set L := closedBall 0 r
  have : CompleteSpace s := isClosed_closedBall.completeSpace_coe
  have hmem : ∀ x : s, F x ∈ s := fun x =>
    mem_closedBall_zero_iff.mpr (hmaps x (mem_closedBall_zero_iff.mp x.2))
  let f : s → s := fun x => ⟨F x, hmem x⟩
  have hf : ContractingWith ⟨q, hq0⟩ f := by
    refine ⟨by exact_mod_cast hq1, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
    have hx : ‖(x : L)‖ ≤ r := mem_closedBall_zero_iff.mp x.2
    have hy : ‖(y : L)‖ ≤ r := mem_closedBall_zero_iff.mp y.2
    change dist (F x) (F y) ≤ q * dist (x : L) (y : L)
    rw [dist_eq_norm, dist_eq_norm]
    exact hlip x y hx hy
  have : Nonempty s := ⟨⟨0, mem_closedBall_self hr0⟩⟩
  set h₀ := ContractingWith.fixedPoint f hf with hh₀
  have hfix : F h₀ = h₀ := congrArg Subtype.val (ContractingWith.fixedPoint_isFixedPt hf)
  have hG0 : G.eval (h₀ : L) = 0 := by
    have e : (h₀ : L) = -(c₀ / c₁) - T.eval (h₀ : L) / c₁ := hfix.symm
    rw [hGT]
    calc c₀ + c₁ * (h₀ : L) + T.eval (h₀ : L)
        = c₀ + c₁ * (-(c₀ / c₁) - T.eval (h₀ : L) / c₁) + T.eval (h₀ : L) := by rw [← e]
      _ = 0 := by field_simp; ring
  have hh₀ : ‖(h₀ : L)‖ ≤ r := mem_closedBall_zero_iff.mp h₀.2
  have hderiv : Q.derivative.eval ((h₀ : L) + t₀) ≠ 0 := by
    have hGd : derivative G = taylor t₀ (derivative Q) := by
      rw [hG, taylor_apply, taylor_apply, derivative_comp, derivative_add, derivative_X,
        derivative_C, add_zero, one_mul]
    have hG' : derivative G = C c₁ + derivative T := by
      simp only [T, derivative_sub, derivative_C, derivative_mul, derivative_X, mul_one,
        zero_mul, zero_add, sub_zero]
      ring
    have hS : ∀ k, ‖(derivative T).coeff k‖ ≤ M := by
      intro k
      rw [coeff_derivative, norm_mul]
      calc ‖T.coeff (k + 1)‖ * ‖((k : L) + 1)‖ ≤ M * 1 := by
            refine mul_le_mul (hT _) ?_ (norm_nonneg _) hM0
            exact_mod_cast IsUltrametricDist.norm_natCast_le_one L (k + 1)
        _ = M := mul_one M
    have hS0 : (derivative T).coeff 0 = 0 := by
      rw [coeff_derivative, hlow 1 (by norm_num), zero_mul]
    have hsm : ‖(derivative T).eval (h₀ : L)‖ < ‖c₁‖ := by
      calc ‖(derivative T).eval (h₀ : L)‖ ≤ M * ‖(h₀ : L)‖ :=
            norm_eval_le_linear _ hM0 hS hS0 (hh₀.trans hr1)
        _ ≤ M * r := by gcongr
        _ = q * ‖c₁‖ := by rw [hq]; field_simp
        _ < 1 * ‖c₁‖ := by gcongr
        _ = ‖c₁‖ := one_mul _
    rw [← taylor_eval, ← hGd, hG', eval_add, eval_C]
    intro h0
    have : (derivative T).eval (h₀ : L) = -c₁ := by linear_combination h0
    rw [this, norm_neg] at hsm
    exact lt_irrefl _ hsm
  refine ⟨h₀ + t₀, ?_, ?_, hderiv⟩
  · rw [← taylor_eval]
    exact hG0
  · rw [add_sub_cancel_right]
    exact hh₀

end UltrametricNewton

variable {K : Type*} [NontriviallyNormedField K]

/-- Over a henselian valued field, a simple root in the completion of a polynomial with
coefficients in the field lies in the field. -/
theorem exists_eq_of_simple_root_completion (hK : IsHenselianValuedField K) (Q : K[X])
    (τ : UniformSpace.Completion K) (hτ : (Q.map (algebraMap K _)).eval τ = 0)
    (hτ' : (Q.map (algebraMap K _)).derivative.eval τ ≠ 0) :
    ∃ t : K, algebraMap K (UniformSpace.Completion K) t = τ := by
  have hQ : Q ≠ 0 := by
    rintro rfl
    simp at hτ'
  have haeval : aeval τ Q = 0 := by rwa [aeval_def, eval₂_eq_eval_map]
  have hint : IsIntegral K τ := ⟨Q * C Q.leadingCoeff⁻¹, monic_mul_leadingCoeff_inv hQ,
    by rw [eval₂_mul, ← aeval_def, haeval, zero_mul]⟩
  have hsep : IsSeparable K τ := by
    obtain ⟨h, hh⟩ := minpoly.dvd K τ haeval
    refine (Polynomial.separable_iff_derivative_ne_zero (minpoly.irreducible hint)).mpr ?_
    intro hd
    have hp0 : ((minpoly K τ).map (algebraMap K _)).eval τ = 0 := by
      rw [← eval₂_eq_eval_map, ← aeval_def, minpoly.aeval]
    apply hτ'
    rw [hh, Polynomial.map_mul, derivative_mul, eval_add, eval_mul, eval_mul, hp0, zero_mul,
      add_zero, Polynomial.derivative_map, hd, Polynomial.map_zero, eval_zero, zero_mul]
  have hmem : τ ∈ separableClosure K (UniformSpace.Completion K) :=
    mem_separableClosure_iff.mpr hsep
  rw [separableClosure_completion_eq_bot K hK, IntermediateField.mem_bot] at hmem
  obtain ⟨t, ht⟩ := hmem
  exact ⟨t, ht⟩

/-- **Newton root lemma over a henselian ultrametric field** (no completeness): a polynomial
`Q` over `K` with `‖Q(t₀)‖ ≤ ‖Q'(t₀)‖` and `M ‖Q(t₀)‖ < ‖Q'(t₀)‖²`, where `M` bounds the
higher Taylor coefficients at `t₀`, has a root in `K` within `‖Q(t₀)‖ / ‖Q'(t₀)‖` of `t₀`. -/
theorem exists_root_of_isHenselianValuedField (hK : IsHenselianValuedField K)
    [IsUltrametricDist K] (Q : K[X]) (t₀ : K) {M : ℝ}
    (hM : ∀ k, 2 ≤ k → ‖(taylor t₀ Q).coeff k‖ ≤ M)
    (h01 : ‖Q.eval t₀‖ ≤ ‖Q.derivative.eval t₀‖)
    (hsmall : M * ‖Q.eval t₀‖ < ‖Q.derivative.eval t₀‖ ^ 2) :
    ∃ τ : K, Q.eval τ = 0 ∧ ‖τ - t₀‖ ≤ ‖Q.eval t₀‖ / ‖Q.derivative.eval t₀‖ := by
  let := completionNontriviallyNormedField K
  let ι : K →+* UniformSpace.Completion K := algebraMap K _
  have hι : ∀ x : K, ‖ι x‖ = ‖x‖ := fun x => UniformSpace.Completion.norm_coe x
  have hev : ∀ (P : K[X]) (x : K), (P.map ι).eval (ι x) = ι (P.eval x) :=
    fun P x => by rw [eval_map, eval₂_hom]
  obtain ⟨τ, hτ, hτn, hτ'⟩ := UltrametricNewton.exists_root (Q.map ι) (ι t₀) (M := M)
    (fun k hk => by rw [← map_taylor, coeff_map, hι]; exact hM k hk)
    (by rw [derivative_map, hev, hev, hι, hι]; exact h01)
    (by rw [derivative_map, hev, hev, hι, hι]; exact hsmall)
  obtain ⟨t, rfl⟩ := exists_eq_of_simple_root_completion hK Q τ hτ hτ'
  refine ⟨t, ι.injective (by rw [← hev, map_zero]; exact hτ), ?_⟩
  rw [derivative_map, hev, hev, hι, hι, ← map_sub, hι] at hτn
  exact hτn

end Langlands.AlgebraicGeometry.PointTopology
