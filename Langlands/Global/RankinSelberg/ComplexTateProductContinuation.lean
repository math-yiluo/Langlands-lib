import Langlands.Global.RankinSelberg.ComplexTateCoordinateReflection

/-! # Entire continuation of normalized product Tate integrals -/

noncomputable section

open Complex Filter Set
open scoped SchwartzMap Topology

namespace Langlands.Global.RankinSelbergGlobal.ComplexTateProduct

variable {n : ℕ}

private def positiveOutside (S : Finset (Fin n)) (u : Fin n → ℂ) : Prop :=
  ∀ j ∉ S, 0 < (u j).re

private abbrev TateFamily (n : ℕ) := 𝓢(Fin n → ℂ, ℂ) → (Fin n → ℤ) → (Fin n → ℂ) → ℂ

private def ExtendsOn (S : Finset (Fin n)) (H : TateFamily n) : Prop :=
  (∀ F m t c s, positiveOutside S (affineParameter t c s) →
    AnalyticAt ℂ (fun w => H F m (affineParameter t c w)) s) ∧
  ∀ F m u, (∀ j, 0 < (u j).re) → H F m u = normalizedZeta F m u

private theorem analyticAt_normalizedZeta (F : 𝓢(Fin n → ℂ, ℂ)) (m : Fin n → ℤ)
    (t : Fin n → ℂ) (c : Fin n → ℝ) (s : ℂ) (hs : ∀ j, 0 < (affineParameter t c s j).re) :
    AnalyticAt ℂ (fun w => normalizedZeta F m (affineParameter t c w)) s := by
  unfold normalizedZeta
  refine (Finset.univ.analyticAt_fun_prod fun j _ => ?_).mul
    (complexTateProductHolomorphy n F m t c s hs)
  have hp : AnalyticAt ℂ (fun w => affineParameter t c w j + (m j).natAbs / 2) s :=
    (analyticAt_const.add (analyticAt_const.mul analyticAt_id)).add analyticAt_const
  exact (differentiable_Gammaℂ_inv.analyticAt _).comp hp

private theorem continuous_re_affineParameter (t : Fin n → ℂ) (c : Fin n → ℝ) (j : Fin n) :
    Continuous (fun w => (affineParameter t c w j).re) :=
  continuous_re.comp (continuous_const.add (continuous_const.mul continuous_id))

private theorem eventually_positiveOutside (S : Finset (Fin n)) (t : Fin n → ℂ) (c : Fin n → ℝ)
    {s : ℂ} (hs : positiveOutside S (affineParameter t c s)) :
    ∀ᶠ w in 𝓝 s, positiveOutside S (affineParameter t c w) := by
  apply Filter.eventually_all.mpr
  intro j
  by_cases hj : j ∈ S
  · exact .of_forall fun _ h => (h hj).elim
  · have hnear : {w | 0 < (affineParameter t c w j).re} ∈ 𝓝 s :=
      (isOpen_lt continuous_const (continuous_re_affineParameter t c j)).mem_nhds (hs j hj)
    exact Filter.Eventually.mono hnear fun _ hw _ => hw

private theorem eventually_lt_affineParameter (t : Fin n → ℂ) (c : Fin n → ℝ) (i : Fin n)
    {s : ℂ} (hs : (affineParameter t c s i).re < 1) :
    ∀ᶠ w in 𝓝 s, (affineParameter t c w i).re < 1 :=
  (isOpen_lt (continuous_re_affineParameter t c i) continuous_const).mem_nhds hs

private theorem reflectedParameter_affine (i : Fin n) (t : Fin n → ℂ) (c : Fin n → ℝ) (s : ℂ) :
    reflectedParameter i (affineParameter t c s) =
      affineParameter (reflectedParameter i t) (Function.update c i (-c i)) s := by
  funext j
  by_cases hj : j = i
  · subst j
    simp only [reflectedParameter, affineParameter, Function.update_self, ofReal_neg]
    ring
  · simp [reflectedParameter, affineParameter, Function.update_of_ne hj]

private theorem positiveOutside_of_insert {S : Finset (Fin n)} {i : Fin n} {u : Fin n → ℂ}
    (hu : positiveOutside (insert i S) u) (hi : 0 < (u i).re) : positiveOutside S u := by
  intro j hj
  by_cases h : j = i
  · rwa [h]
  · exact hu j (by simp [h, hj])

private theorem reflected_positiveOutside_of_insert {S : Finset (Fin n)} {i : Fin n} {u : Fin n → ℂ}
    (hu : positiveOutside (insert i S) u) (hi : (u i).re < 1) :
    positiveOutside S (reflectedParameter i u) := by
  intro j hj
  by_cases h : j = i
  · subst j
    simpa [reflectedParameter] using sub_pos.mpr hi
  · simpa [reflectedParameter, Function.update_of_ne h] using hu j (by simp [h, hj])

private theorem positiveOutside_insert_of_positiveOutside {S : Finset (Fin n)} {i : Fin n} {u : Fin n → ℂ}
    (hu : positiveOutside S u) : positiveOutside (insert i S) u :=
  fun j hj => hu j (fun hjS => hj (Finset.mem_insert_of_mem hjS))

private theorem analyticAt_reflected {S : Finset (Fin n)} {H : TateFamily n} (hH : ExtendsOn S H)
    (F : 𝓢(Fin n → ℂ, ℂ)) (m : Fin n → ℤ) (i : Fin n) (t : Fin n → ℂ) (c : Fin n → ℝ) (s : ℂ)
    (hs : positiveOutside S (reflectedParameter i (affineParameter t c s))) :
    AnalyticAt ℂ (fun w => H F m (reflectedParameter i (affineParameter t c w))) s := by
  rw [reflectedParameter_affine] at hs
  simpa only [reflectedParameter_affine] using
    hH.1 F m (reflectedParameter i t) (Function.update c i (-c i)) s hs

private theorem reflection_on_overlap {S : Finset (Fin (n + 1))} {H : TateFamily (n + 1)}
    (hH : ExtendsOn S H) (F : 𝓢(Fin (n + 1) → ℂ, ℂ)) (m : Fin (n + 1) → ℤ)
    (i : Fin (n + 1)) (hiS : i ∉ S) (u : Fin (n + 1) → ℂ)
    (hu : positiveOutside S u) (hi : (u i).re < 1) :
    H (coordinateFourier F i) (reflectedWeight i m) (reflectedParameter i u) =
      I ^ (m i).natAbs * H F m u := by
  classical
  let c (j : Fin (n + 1)) : ℝ := if j ∈ S then 1 + |(u j).re| else 0
  let U := affineParameter u c
  have hU_out (w : ℂ) : positiveOutside S (U w) := by
    intro j hj
    simpa [U, affineParameter, c, hj] using hu j hj
  have hU_i (w : ℂ) : U w i = u i := by simp [U, affineParameter, c, hiS]
  have ha : AnalyticOnNhd ℂ (fun w => H (coordinateFourier F i) (reflectedWeight i m)
      (reflectedParameter i (U w))) univ := by
    intro w _
    apply analyticAt_reflected hH
    exact reflected_positiveOutside_of_insert (positiveOutside_insert_of_positiveOutside (hU_out w))
      (show (U w i).re < 1 by rwa [hU_i w])
  have hb : AnalyticOnNhd ℂ (fun w => I ^ (m i).natAbs * H F m (U w)) univ :=
    fun w _ => analyticAt_const.mul (hH.1 F m u c w (hU_out w))
  have h1 (j : Fin (n + 1)) : 0 < (U 1 j).re := by
    by_cases hj : j ∈ S
    · simp only [U, affineParameter, c, ite_eq_left hj, mul_one, add_re, ofReal_re]
      linarith [neg_abs_le (u j).re]
    · exact hU_out 1 j hj
  have hevent : (fun w => H (coordinateFourier F i) (reflectedWeight i m)
      (reflectedParameter i (U w))) =ᶠ[𝓝 (1 : ℂ)] fun w => I ^ (m i).natAbs * H F m (U w) := by
    filter_upwards [eventually_positiveOutside ∅ u c (s := 1) (fun j _ => h1 j)] with w hw
    have hw' (j : Fin (n + 1)) : 0 < (U w j).re := hw j (Finset.notMem_empty j)
    have hi' : (U w i).re < 1 := by simpa only [hU_i w] using hi
    have hwr (j : Fin (n + 1)) : 0 < (reflectedParameter i (U w) j).re :=
      reflected_positiveOutside_of_insert (S := ∅) (fun j _ => hw' j) hi' j (Finset.notMem_empty j)
    rw [hH.2 _ _ _ hwr, hH.2 _ _ _ hw']
    exact normalizedZeta_coordinateFourier F i m (U w) hw' hi'
  have he := congrFun (ha.eq_of_eventuallyEq hb hevent) 0
  have hU₀ : U 0 = u := by funext j; simp [U, affineParameter]
  change H (coordinateFourier F i) (reflectedWeight i m) (reflectedParameter i (U 0)) =
    I ^ (m i).natAbs * H F m (U 0) at he
  rwa [hU₀] at he

private theorem exists_extendsOn (S : Finset (Fin (n + 1))) :
    ∃ H : TateFamily (n + 1), ExtendsOn S H := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      refine ⟨fun F m u => normalizedZeta F m u, ?_, fun _ _ _ _ => rfl⟩
      intro F m t c s hs
      exact analyticAt_normalizedZeta F m t c s fun j => hs j (Finset.notMem_empty j)
  | @insert i S hiS ih =>
      obtain ⟨H, hH⟩ := ih
      let G : TateFamily (n + 1) := fun F m u =>
        if 0 < (u i).re then H F m u else
          (I ^ (m i).natAbs)⁻¹ * H (coordinateFourier F i) (reflectedWeight i m) (reflectedParameter i u)
      refine ⟨G, ?_, fun F m u hu => ?_⟩
      · intro F m t c s hs
        let U := affineParameter t c
        by_cases hi : 0 < (U s i).re
        · refine (hH.1 F m t c s (positiveOutside_of_insert hs hi)).congr ?_
          have hn : {w | 0 < (U w i).re} ∈ 𝓝 s :=
            (isOpen_lt continuous_const (continuous_re_affineParameter t c i)).mem_nhds hi
          filter_upwards [hn] with w hw
          exact (ite_eq_left hw).symm
        · have hi' : (U s i).re < 1 := lt_of_le_of_lt (le_of_not_gt hi) zero_lt_one
          have har := analyticAt_reflected hH (coordinateFourier F i) (reflectedWeight i m) i t c s
            (reflected_positiveOutside_of_insert hs hi')
          have hphase : AnalyticAt ℂ (fun _ : ℂ => (I ^ (m i).natAbs)⁻¹) s := analyticAt_const
          refine (hphase.mul har).congr ?_
          filter_upwards [eventually_positiveOutside (insert i S) t c hs,
            eventually_lt_affineParameter t c i hi'] with w hw hwi
          change _ = G F m (U w)
          by_cases hpos : 0 < (U w i).re
          · dsimp only [G, Pi.mul_apply]
            rw [ite_eq_left hpos, reflection_on_overlap hH F m i hiS (U w)
              (positiveOutside_of_insert hw hpos) hwi, ← mul_assoc,
              inv_mul_cancel₀ (pow_ne_zero _ I_ne_zero), one_mul]
          · exact (ite_eq_right hpos).symm
      · exact (ite_eq_left (hu i)).trans (hH.2 F m u hu)

/-- The normalized product Tate integral has an entire extension along every affine spectral line
with real slopes, even when the coordinates have different slopes. -/
def ComplexTateProductContinuationStatement : Prop :=
  ∀ (n : ℕ) (F : 𝓢(Fin n → ℂ, ℂ)) (m : Fin n → ℤ) (t : Fin n → ℂ) (c : Fin n → ℝ),
    ∃ N : ℂ → ℂ, Differentiable ℂ N ∧ ∀ s : ℂ,
      (∀ j, 0 < (affineParameter t c s j).re) → N s = normalizedZeta F m (affineParameter t c s)

theorem complexTateProductContinuation : ComplexTateProductContinuationStatement := by
  intro n F m t c
  cases n with
  | zero =>
      refine ⟨fun w => normalizedZeta F m (affineParameter t c w), ?_, fun _ _ => rfl⟩
      exact fun s => (analyticAt_normalizedZeta F m t c s fun j => j.elim0).differentiableAt
  | succ n =>
      obtain ⟨H, hH⟩ := exists_extendsOn (n := n) Finset.univ
      exact ⟨fun w => H F m (affineParameter t c w),
        fun s => (hH.1 F m t c s (by simp [positiveOutside])).differentiableAt,
        fun s hs => hH.2 F m _ hs⟩

/-- An entire normalization extends the product Tate integral by a single function of the
independent exponents. Each restriction to an affine spectral line with real slopes is entire. -/
def IsEntireNormalization {n : ℕ}
    (H : 𝓢(Fin n → ℂ, ℂ) → (Fin n → ℤ) → (Fin n → ℂ) → ℂ) : Prop :=
  (∀ F m t c, Differentiable ℂ (fun s => H F m (affineParameter t c s))) ∧
  ∀ F m u, (∀ j, 0 < (u j).re) → H F m u = normalizedZeta F m u

/-- One normalized function of all the exponents simultaneously realizes the continuations on
every affine spectral line with real slopes. -/
def ComplexTateProductEntireFamilyStatement : Prop :=
  ∀ n : ℕ, ∃ H : 𝓢(Fin (n + 1) → ℂ, ℂ) → (Fin (n + 1) → ℤ) → (Fin (n + 1) → ℂ) → ℂ,
    IsEntireNormalization H

theorem complexTateProductEntireFamily : ComplexTateProductEntireFamilyStatement := by
  intro n
  obtain ⟨H, hH⟩ := exists_extendsOn (n := n) Finset.univ
  exact ⟨H, fun F m t c s => (hH.1 F m t c s (by simp [positiveOutside])).differentiableAt, hH.2⟩

end Langlands.Global.RankinSelbergGlobal.ComplexTateProduct
