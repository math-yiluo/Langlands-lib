import Langlands.Global.RankinSelberg.ComplexTateProductContinuation
import Langlands.Global.RankinSelberg.ArchimedeanGammaBounds
import Langlands.LocalFactor.Archimedean.GammaStripGrowth

/-! # Exponential strip growth of entire normalized complex product Tate integrals -/

noncomputable section

open Complex Filter MeasureTheory Set
open scoped SchwartzMap Topology BigOperators

set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.ComplexTateProduct

open ArchimedeanInverseMellin LocalFactor.Archimedean

variable {n : ℕ}
local notation "J" => Fin (n + 1)
local notation "V" => (J → ℂ)
local notation "TateFamily" => (𝓢(V, ℂ) → (J → ℤ) → V → ℂ)

/-- The common-strip coordinate equation extends to all parameters along affine lines. -/
theorem IsEntireNormalization.reflect_coordinate {H : TateFamily} (hH : IsEntireNormalization H)
    (F : 𝓢(V, ℂ)) (m : J → ℤ) (i : J) (u : V) :
    H (coordinateFourier F i) (reflectedWeight i m) (reflectedParameter i u) =
      I ^ (m i).natAbs * H F m u := by
  let t (j : J) : ℂ := 1 / 2 + (u j).im * I
  let c (j : J) : ℝ := (u j).re - 1 / 2
  let U := affineParameter t c
  have hreflect (s : ℂ) : reflectedParameter i (U s) =
      affineParameter (reflectedParameter i t) (Function.update c i (-c i)) s := by
    funext j
    by_cases h : j = i
    · subst j
      simp only [reflectedParameter, Function.update_self, affineParameter, U, ofReal_neg]
      ring
    · simp [reflectedParameter, Function.update_of_ne h, affineParameter, U]
  have hU₀ (j : J) : (U 0 j).re = 1 / 2 := by
    simp [U, affineParameter, t, Complex.mul_re]
  have hU₁ : U 1 = u := by
    funext j
    dsimp [U, affineParameter, t, c]
    rw [mul_one, ofReal_sub, ofReal_div, ofReal_one, ofReal_ofNat]
    calc
      _ = (u j).re + (u j).im * I := by ring
      _ = _ := re_add_im _
  have hleft : Differentiable ℂ (fun s =>
      H (coordinateFourier F i) (reflectedWeight i m) (reflectedParameter i (U s))) := by
    simpa only [hreflect] using hH.1 (coordinateFourier F i) (reflectedWeight i m)
      (reflectedParameter i t) (Function.update c i (-c i))
  have hright : Differentiable ℂ (fun s => I ^ (m i).natAbs * H F m (U s)) :=
    (hH.1 F m t c).const_mul _
  have hc (j : J) : Continuous (fun s => (U s j).re) :=
    continuous_re.comp (continuous_const.add (continuous_const.mul continuous_id))
  have hpos : ∀ᶠ s in 𝓝 (0 : ℂ), ∀ j, 0 < (U s j).re := by
    refine eventually_all.mpr fun j => (isOpen_lt continuous_const (hc j)).mem_nhds ?_
    show 0 < (U 0 j).re
    rw [hU₀]
    norm_num
  have hsmall : ∀ᶠ s in 𝓝 (0 : ℂ), (U s i).re < 1 := by
    refine (isOpen_lt (hc i) continuous_const).mem_nhds ?_
    show (U 0 i).re < 1
    rw [hU₀]
    norm_num
  have heq : (fun s => H (coordinateFourier F i) (reflectedWeight i m) (reflectedParameter i (U s)))
      =ᶠ[𝓝 (0 : ℂ)] fun s => I ^ (m i).natAbs * H F m (U s) := by
    filter_upwards [hpos, hsmall] with s hs hsi
    have hpos' (j : J) : 0 < (reflectedParameter i (U s) j).re := by
      by_cases h : j = i
      · subst j
        simpa [reflectedParameter] using sub_pos.mpr hsi
      · simpa [reflectedParameter, Function.update_of_ne h] using hs j
    rw [hH.2 _ _ _ hpos', hH.2 _ _ _ hs]
    exact normalizedZeta_coordinateFourier F i m (U s) hs hsi
  have h := (show AnalyticOnNhd ℂ _ univ from fun s _ => hleft.analyticAt s).eq_of_eventuallyEq
    (fun s _ => hright.analyticAt s) heq
  simpa only [hU₁] using congrFun h (1 : ℂ)

private theorem norm_zeta_le_on_positive_box (F : 𝓢(V, ℂ)) (m : J → ℤ) {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ u : V, (∀ j, a ≤ (u j).re) → (∀ j, (u j).re ≤ b) →
      ‖zeta F m u‖ ≤ B := by
  classical
  let v (p : J → Bool) (j : J) : ℂ := if p j then (a : ℂ) else (b : ℂ)
  let M (z : V) := ∑ p : J → Bool, ‖integrand F m (v p) z‖
  have hM : Integrable M volume := by
    apply integrable_finsetSum
    intro p _
    apply Integrable.norm (integrable_integrand F m _)
    intro j
    by_cases h : p j <;> simp [v, h, ha, hb]
  refine ⟨∫ z, M z, integral_nonneg (fun z => Finset.sum_nonneg fun _ _ => norm_nonneg _),
    fun u hlo hhi => ?_⟩
  unfold zeta
  refine norm_integral_le_of_norm_le hM (Eventually.of_forall fun z => ?_)
  let p (j : J) := decide (‖z j‖ ≤ 1)
  apply le_trans _ (Finset.single_le_sum (f := fun p => ‖integrand F m (v p) z‖)
    (fun _ _ => norm_nonneg _) (Finset.mem_univ p))
  simp only [integrand, norm_mul, norm_prod]
  refine mul_le_mul_of_nonneg_left (Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun j _ => ?_)
    (norm_nonneg _)
  by_cases hz : z j = 0
  · simp [additiveWeight, hz]
  · rw [norm_additiveWeight hz, norm_additiveWeight hz]
    by_cases h : ‖z j‖ ≤ 1
    · simp only [v, p, decide_eq_true h, ite_true, ofReal_re]
      exact Real.rpow_le_rpow_of_exponent_ge (norm_pos_iff.mpr hz) h (by linarith [hlo j])
    · simp only [v, p, decide_eq_false h, Bool.false_eq_true, ite_false, ofReal_re]
      exact Real.rpow_le_rpow_of_exponent_le (le_of_not_ge h) (by linarith [hhi j])

private theorem norm_normalizedZeta_on_positive_box (F : 𝓢(V, ℂ)) (m : J → ℤ) {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) :
    ∃ C K : ℝ, 0 ≤ C ∧ 0 ≤ K ∧ ∀ u : V, (∀ j, a ≤ (u j).re) → (∀ j, (u j).re ≤ b) →
      ‖normalizedZeta F m u‖ ≤ C * Real.exp (K * ∑ j, |(u j).im|) := by
  obtain ⟨B, hB, hZ⟩ := norm_zeta_le_on_positive_box F m ha hb
  have hG (j : J) : StripExpType (gammaNormalizer (m j)) :=
    inv_Gammaℂ_stripExpType.comp_add _
  choose C K hC hK hγ using fun j => hG j a b
  let L := ∑ j, K j
  refine ⟨(∏ j, C j) * B, L, mul_nonneg (Finset.prod_nonneg fun j _ => hC j) hB,
    Finset.sum_nonneg (fun j _ => hK j), fun u hlo hhi => ?_⟩
  unfold normalizedZeta
  rw [norm_mul, norm_prod]
  have hprod : (∏ j, ‖gammaNormalizer (m j) (u j)‖) ≤
      (∏ j, C j) * Real.exp (L * ∑ j, |(u j).im|) := by
    rw [Finset.mul_sum, Real.exp_sum, ← Finset.prod_mul_distrib]
    refine Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun j hj => ?_
    have hg := hγ j (u j).re (hlo j) (hhi j) (u j).im
    rw [re_add_im] at hg
    exact hg.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_right (Finset.single_le_sum (fun j _ => hK j) hj) (abs_nonneg _))) (hC j))
  exact (mul_le_mul hprod (hZ u hlo hhi) (norm_nonneg _)
    (mul_nonneg (Finset.prod_nonneg fun j _ => hC j) (Real.exp_pos _).le)).trans_eq (by ring)

private theorem norm_entireNormalization_on_box {H : TateFamily} (hH : IsEntireNormalization H)
    (S : Finset J) (F : 𝓢(V, ℂ)) (m : J → ℤ) (a b : ℝ) :
    ∃ C K : ℝ, 0 ≤ C ∧ 0 ≤ K ∧ ∀ u : V, (∀ j, a ≤ (u j).re) → (∀ j, (u j).re ≤ b) →
      (∀ j ∉ S, (1 / 2 : ℝ) ≤ (u j).re) →
      ‖H F m u‖ ≤ C * Real.exp (K * ∑ j, |(u j).im|) := by
  classical
  induction S using Finset.induction_on generalizing F m a b with
  | empty =>
    obtain ⟨C, K, hC, hK, hbound⟩ := norm_normalizedZeta_on_positive_box F m
      (a := 1 / 2) (b := max b 1) (by norm_num) (lt_of_lt_of_le zero_lt_one (le_max_right _ _))
    refine ⟨C, K, hC, hK, fun u _ hhi hlow => ?_⟩
    have hl (j : J) := hlow j (Finset.notMem_empty j)
    rw [hH.2 _ _ _ (fun j => lt_of_lt_of_le (by norm_num) (hl j))]
    exact hbound u hl (fun j => (hhi j).trans (le_max_left _ _))
  | insert i S hi ih =>
    obtain ⟨C, K, hC, hK, hbound⟩ := ih F m a b
    obtain ⟨D, L, hD, hL, hbound'⟩ := ih (coordinateFourier F i) (reflectedWeight i m)
      a (max b (1 - a))
    let A := max C D
    let B := max K L
    have hA : 0 ≤ A := hC.trans (le_max_left _ _)
    have hB : 0 ≤ B := hK.trans (le_max_left _ _)
    refine ⟨A, B, hA, hB, fun u hlo hhi hRest => ?_⟩
    have hIm : 0 ≤ ∑ j, |(u j).im| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    by_cases hn : (1 / 2 : ℝ) ≤ (u i).re
    · apply (hbound u hlo hhi (fun j hj => ?_)).trans
        (mul_le_mul (le_max_left _ _) (Real.exp_le_exp.mpr
          (mul_le_mul_of_nonneg_right (le_max_left _ _) hIm)) (Real.exp_pos _).le hA)
      by_cases he : j = i
      · exact he ▸ hn
      · exact hRest j (fun h => (Finset.mem_insert.mp h).elim he hj)
    · let v := reflectedParameter i u
      have hvi : (v i).re = 1 - (u i).re := by simp [v, reflectedParameter]
      have hvj (j : J) (h : j ≠ i) : v j = u j := Function.update_of_ne h _ _
      have hlo' (j : J) : a ≤ (v j).re := by
        by_cases he : j = i
        · subst j
          rw [hvi]
          linarith [hlo i, lt_of_not_ge hn]
        · exact (hvj j he).symm ▸ hlo j
      have hhi' (j : J) : (v j).re ≤ max b (1 - a) := by
        by_cases he : j = i
        · subst j
          rw [hvi]
          exact (sub_le_sub_left (hlo i) 1).trans (le_max_right _ _)
        · rw [hvj j he]
          exact (hhi j).trans (le_max_left _ _)
      have hRest' (j : J) (hj : j ∉ S) : (1 / 2 : ℝ) ≤ (v j).re := by
        by_cases he : j = i
        · subst j
          rw [hvi]
          linarith [lt_of_not_ge hn]
        · rw [hvj j he]
          exact hRest j (fun h => (Finset.mem_insert.mp h).elim he hj)
      have hnorm : ‖H (coordinateFourier F i) (reflectedWeight i m) v‖ = ‖H F m u‖ := by
        rw [hH.reflect_coordinate, norm_mul, norm_pow, norm_I, one_pow, one_mul]
      have hsum : (∑ j, |(v j).im|) = ∑ j, |(u j).im| := by
        apply Finset.sum_congr rfl
        intro j _
        by_cases he : j = i
        · subst j
          simp [v, reflectedParameter]
        · rw [hvj j he]
      have hg := hbound' v hlo' hhi' hRest'
      rw [hnorm, hsum] at hg
      exact hg.trans (mul_le_mul (le_max_right _ _) (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_right (le_max_right _ _) hIm)) (Real.exp_pos _).le hA)

/-- Every affine specialization of an entire normalized complex product Tate family has
exponential growth in vertical strips. -/
def ComplexTateProductStripGrowthStatement : Prop :=
  ∀ (n : ℕ) (H : 𝓢(Fin (n + 1) → ℂ, ℂ) → (Fin (n + 1) → ℤ) → (Fin (n + 1) → ℂ) → ℂ),
    IsEntireNormalization H →
    ∀ F m t c, HasStripExponentialGrowth (fun s => H F m (affineParameter t c s))

theorem complexTateProductStripGrowth : ComplexTateProductStripGrowthStatement := by
  intro n H hH F m t c a b
  let M := |a| + |b|
  let R := ∑ j, (|(t j).re| + |c j| * M)
  let D := ∑ j, |(t j).im|
  let L := ∑ j, |c j|
  obtain ⟨C, K, hC, hK, hbound⟩ := norm_entireNormalization_on_box hH Finset.univ F m (-R) R
  refine ⟨C * Real.exp (K * D), K * L, 0, by positivity, by positivity, fun s hlo hhi _ => ?_⟩
  let u := affineParameter t c s
  have hM : |s.re| ≤ M := abs_le.mpr
    ⟨by dsimp [M]; linarith [neg_abs_le a, abs_nonneg b],
      by dsimp [M]; linarith [le_abs_self b, abs_nonneg a]⟩
  have hR (j : Fin (n + 1)) : |(u j).re| ≤ R := by
    simp only [u, affineParameter, add_re, re_ofReal_mul]
    calc
      _ ≤ |(t j).re| + |c j| * |s.re| := by
        simpa only [abs_mul] using (abs_add_le ((t j).re) (c j * s.re))
      _ ≤ |(t j).re| + |c j| * M := by
        gcongr
      _ ≤ R := Finset.single_le_sum (f := fun j => |(t j).re| + |c j| * M)
        (fun j _ => by positivity) (Finset.mem_univ j)
  have hI : (∑ j, |(u j).im|) ≤ D + L * |s.im| := by
    dsimp [D, L]
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro j _
    simp only [u, affineParameter, add_im, im_ofReal_mul]
    simpa only [abs_mul] using abs_add_le ((t j).im) (c j * s.im)
  have hg := hbound u (fun j => (abs_le.mp (hR j)).1) (fun j => (abs_le.mp (hR j)).2)
    (fun j hj => (hj (Finset.mem_univ j)).elim)
  refine hg.trans (le_trans (mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hI hK)) hC) ?_)
  simp only [mul_add, mul_assoc, Real.exp_add, le_refl]

/-- The normalized Tate product strip estimate with the rank fixed. -/
def ComplexTateProductStripGrowthAtRank : Prop :=
  ∀ H : 𝓢(Fin (n + 1) → ℂ, ℂ) → (Fin (n + 1) → ℤ) → (Fin (n + 1) → ℂ) → ℂ, IsEntireNormalization H →
    ∀ (F : 𝓢(Fin (n + 1) → ℂ, ℂ)) (m : Fin (n + 1) → ℤ) (t : Fin (n + 1) → ℂ) (c : Fin (n + 1) → ℝ),
      HasStripExponentialGrowth (fun s => H F m (affineParameter t c s))

/-- Specialize the all-ranks estimate to the specified rank. -/
theorem complexTateProductStripGrowthAtRank : ComplexTateProductStripGrowthAtRank (n := n) :=
  complexTateProductStripGrowth n

end Langlands.Global.RankinSelbergGlobal.ComplexTateProduct
