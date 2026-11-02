import Langlands.Global.Arithmetic.RealRootNeighborhood
import Mathlib.Analysis.AbsoluteValue.Equivalence
import Mathlib.NumberTheory.Padics.PadicNumbers

/-! # Rational approximation in the real and p-adic topologies -/

noncomputable section

namespace Langlands.Global.FieldRealization

open Polynomial
open scoped BigOperators

/-- The usual real absolute value restricted to the rationals. -/
def rationalRealAbv : AbsoluteValue ℚ ℝ :=
  (NormedField.toAbsoluteValue ℝ).comp (algebraMap ℚ ℝ).injective

/-- The p-adic absolute value restricted to the rationals. -/
def rationalPadicAbv (p : ℕ) [Fact p.Prime] : AbsoluteValue ℚ ℝ :=
  (NormedField.toAbsoluteValue (Padic p)).comp (algebraMap ℚ (Padic p)).injective

@[simp] theorem rationalRealAbv_apply (q : ℚ) : rationalRealAbv q = ‖(q : ℝ)‖ := rfl

@[simp] theorem rationalPadicAbv_apply (p : ℕ) [Fact p.Prime] (q : ℚ) :
    rationalPadicAbv p q = ‖(q : Padic p)‖ := rfl

/-- The two absolute values used for simultaneous approximation. -/
def rationalMixedAbv (p : ℕ) [Fact p.Prime] : Bool → AbsoluteValue ℚ ℝ
  | false => rationalRealAbv
  | true => rationalPadicAbv p

theorem rationalMixedAbv_isNontrivial (p : ℕ) [hp : Fact p.Prime] (i : Bool) :
    (rationalMixedAbv p i).IsNontrivial := by
  cases i
  · refine ⟨2, by norm_num, ?_⟩
    norm_num [rationalMixedAbv]
  · refine ⟨(p : ℚ), Nat.cast_ne_zero.mpr hp.1.ne_zero, ne_of_lt ?_⟩
    simpa [rationalMixedAbv] using (Padic.norm_p_lt_one (p := p))

theorem rationalRealAbv_not_isEquiv_padic (p : ℕ) [hp : Fact p.Prime] :
    ¬ rationalRealAbv.IsEquiv (rationalPadicAbv p) := by
  intro h
  have hlt : rationalPadicAbv p (p : ℚ) < 1 := by
    simpa using (Padic.norm_p_lt_one (p := p))
  have hr := (h.lt_one_iff (x := (p : ℚ))).mpr hlt
  simp only [rationalRealAbv_apply, Rat.cast_natCast, Real.norm_natCast] at hr
  have hge : (1 : ℝ) ≤ p := by exact_mod_cast hp.1.one_lt.le
  exact (not_lt_of_ge hge) hr

theorem rationalMixedAbv_pairwise (p : ℕ) [Fact p.Prime] :
    Pairwise fun i j => ¬ (rationalMixedAbv p i).IsEquiv (rationalMixedAbv p j) := by
  intro i j hne
  cases i <;> cases j
  · exact (hne rfl).elim
  · exact rationalRealAbv_not_isEquiv_padic p
  · exact fun h => rationalRealAbv_not_isEquiv_padic p h.symm
  · exact (hne rfl).elim

/-- A rational number can approximate a real and a p-adic number simultaneously. -/
theorem exists_rat_real_padic_approx (p : ℕ) [Fact p.Prime]
    (a : Padic p) (b : ℝ) {εp εr : ℝ} (hp : 0 < εp) (hr : 0 < εr) :
    ∃ q : ℚ, ‖(q : Padic p) - a‖ < εp ∧ ‖(q : ℝ) - b‖ < εr := by
  obtain ⟨ap, hap⟩ := Metric.denseRange_iff.mp
    (Padic.denseRange_ratCast (p := p)) a (εp / 2) (half_pos hp)
  obtain ⟨br, hbr⟩ := Metric.denseRange_iff.mp
    (Rat.denseRange_cast (𝕜 := ℝ)) b (εr / 2) (half_pos hr)
  let v := rationalMixedAbv p
  let c : (i : Bool) → WithAbs (v i) := fun i =>
    WithAbs.toAbs (v i) (if i then ap else br)
  have hδ : 0 < min (εp / 2) (εr / 2) := lt_min (half_pos hp) (half_pos hr)
  obtain ⟨q, hq⟩ := Metric.denseRange_iff.mp
    (AbsoluteValue.denseRange_algebraMap_pi (rationalMixedAbv_isNontrivial p)
      (rationalMixedAbv_pairwise p)) c _ hδ
  have hcoord := (dist_pi_lt_iff hδ).mp hq
  have hqp : ‖(q : Padic p) - (ap : Padic p)‖ < εp / 2 := by
    have ht := (hcoord true).trans_le (min_le_left _ _)
    change dist (WithAbs.toAbs (rationalPadicAbv p) ap)
      (WithAbs.toAbs (rationalPadicAbv p) q) < εp / 2 at ht
    rw [dist_eq_norm, ← WithAbs.toAbs_sub, WithAbs.norm_toAbs_eq] at ht
    simpa only [rationalPadicAbv_apply, Rat.cast_sub, norm_sub_rev] using ht
  have hqr : ‖(q : ℝ) - (br : ℝ)‖ < εr / 2 := by
    have ht := (hcoord false).trans_le (min_le_right _ _)
    change dist (WithAbs.toAbs rationalRealAbv br)
      (WithAbs.toAbs rationalRealAbv q) < εr / 2 at ht
    rw [dist_eq_norm, ← WithAbs.toAbs_sub, WithAbs.norm_toAbs_eq] at ht
    simpa only [rationalRealAbv_apply, Rat.cast_sub, norm_sub_rev] using ht
  refine ⟨q, ?_, ?_⟩
  · have hap' : ‖(ap : Padic p) - a‖ < εp / 2 := by
      simpa [dist_eq_norm, norm_sub_rev] using hap
    calc
      _ ≤ ‖(q : Padic p) - ap‖ + ‖(ap : Padic p) - a‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ < εp := by linarith
  · have hbr' : ‖(br : ℝ) - b‖ < εr / 2 := by
      simpa [dist_eq_norm, norm_sub_rev] using hbr
    calc
      _ ≤ ‖(q : ℝ) - br‖ + ‖(br : ℝ) - b‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ < εr := by linarith

/-- A rational monic polynomial with prescribed coefficients below its degree. -/
def rationalMonicModel (n : ℕ) (c : ℕ → ℚ) : Polynomial ℚ :=
  X ^ n + ∑ i ∈ Finset.range n, C (c i) * X ^ i

private theorem rationalMonicModel_lower_degree (n : ℕ) (c : ℕ → ℚ) :
    (∑ i ∈ Finset.range n, C (c i) * X ^ i).degree < (n : WithBot ℕ) := by
  simpa only [← Fin.sum_univ_eq_sum_range] using
    (degree_sum_fin_lt (fun i : Fin n => c i.val))

theorem rationalMonicModel_monic (n : ℕ) (c : ℕ → ℚ) :
    (rationalMonicModel n c).Monic :=
  monic_X_pow_add (rationalMonicModel_lower_degree n c)

theorem rationalMonicModel_natDegree (n : ℕ) (c : ℕ → ℚ) :
    (rationalMonicModel n c).natDegree = n := by
  unfold rationalMonicModel
  rw [natDegree_add_eq_left_of_degree_lt]
  · exact natDegree_X_pow n
  · simpa only [degree_X_pow] using rationalMonicModel_lower_degree n c

theorem rationalMonicModel_coeff (n : ℕ) (c : ℕ → ℚ) (k : ℕ) :
    (rationalMonicModel n c).coeff k =
      (if k = n then 1 else 0) + (if k < n then c k else 0) := by
  classical
  simp [rationalMonicModel, coeff_X_pow, eq_comm]

/-- Every monic p-adic polynomial admits a monic rational coefficient approximation
of the same degree whose real image splits with distinct roots. -/
theorem exists_monic_rat_real_split_padic_approx (p : ℕ) [Fact p.Prime]
    (f : Polynomial (Padic p)) (hf : f.Monic) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : Polynomial ℚ, g.Monic ∧ g.natDegree = f.natDegree ∧
      (g.map (algebraMap ℚ ℝ)).Splits ∧ g.Separable ∧
      ∀ k : ℕ, ‖(g.map (algebraMap ℚ (Padic p))).coeff k - f.coeff k‖ < ε := by
  classical
  let n := f.natDegree
  choose c hcP hcR using fun k : ℕ =>
    exists_rat_real_padic_approx p (f.coeff k) ((realRootModel n).coeff k)
      hε (realRootRadius_pos n)
  let g := rationalMonicModel n c
  have hgm : g.Monic := rationalMonicModel_monic n c
  have hgdeg : g.natDegree = n := rationalMonicModel_natDegree n c
  have hcoeffP : ∀ k : ℕ,
      ‖(g.map (algebraMap ℚ (Padic p))).coeff k - f.coeff k‖ < ε := by
    intro k
    rcases lt_trichotomy k n with h | rfl | h
    · simpa [g, coeff_map, rationalMonicModel_coeff, h, ne_of_lt h] using hcP k
    · simp [coeff_map, n, hf, hε, g,
        rationalMonicModel_coeff]
    · have hfk : f.coeff k = 0 := coeff_eq_zero_of_natDegree_lt h
      simp [g, coeff_map, rationalMonicModel_coeff, h.ne', not_lt_of_gt h, hfk, hε]
  have hcoeffR : ∀ k : ℕ,
      ‖(g.map (algebraMap ℚ ℝ)).coeff k - (realRootModel n).coeff k‖ < realRootRadius n := by
    intro k
    rcases lt_trichotomy k n with h | rfl | h
    · simpa [g, coeff_map, rationalMonicModel_coeff, h, ne_of_lt h] using hcR k
    · have hmcoeff : (realRootModel n).coeff n = 1 := by
        simpa only [realRootModel_natDegree] using (realRootModel_monic n).coeff_natDegree
      simp [g, coeff_map, rationalMonicModel_coeff, hmcoeff, realRootRadius_pos n]
    · have hmk : (realRootModel n).coeff k = 0 :=
        coeff_eq_zero_of_natDegree_lt ((realRootModel_natDegree n).symm ▸ h)
      simp [g, coeff_map, rationalMonicModel_coeff, h.ne', not_lt_of_gt h,
        hmk, realRootRadius_pos n]
  have hreal := splits_separable_of_coeff_lt_realRootRadius n
    (g.map (algebraMap ℚ ℝ)) (hgm.map _) (by simpa using hgdeg) hcoeffR
  exact ⟨g, hgm, hgdeg, hreal.1, (separable_map (algebraMap ℚ ℝ)).mp hreal.2, hcoeffP⟩

end Langlands.Global.FieldRealization
