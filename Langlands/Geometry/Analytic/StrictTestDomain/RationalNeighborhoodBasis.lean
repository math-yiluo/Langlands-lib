import Langlands.Geometry.Analytic.StrictTestDomain.BinaryLaurentCover
import Langlands.Geometry.Analytic.Spectrum.LaurentNeighborhoods

/-! # Strict rational neighbourhood bases of spectrum points -/

noncomputable section

universe u

namespace Langlands.Analytic.StrictTestDomain.RationalData

open Filter
open scoped Topology

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {P : PresentedStrictAffinoidAlgebra K}

/-- The rational data of the intersection of a finite list of rational loci. -/
def listInter : List (RationalData K P) → RationalData K P
  | [] => whole K P
  | d :: l => d.inter (listInter l)

theorem mem_locus_listInter (l : List (RationalData K P)) (x : BanachSpectrum P) :
    x ∈ (listInter l).locus ↔ ∀ d ∈ l, x ∈ d.locus := by
  induction l with
  | nil => simp [listInter]
  | cons d l ih =>
    rw [listInter, locus_inter, Set.mem_inter_iff, ih]
    simp

omit [CompleteSpace K] in
/-- A strict upper bound at a point can be replaced by a unit-radius bound on a
monomial `c⁻ᵐ aⁿ` which is still strict at the point and implies the original
bound everywhere. -/
theorem exists_upper_unit_bound {c : K} (hc : 1 < ‖c‖) (x : BanachSpectrum P)
    (a : P) {r : ℝ} (hr : 0 < r) (hxr : x a < r) :
    ∃ f : P, x f < 1 ∧ ∀ y : BanachSpectrum P, y f ≤ 1 → y a ≤ r := by
  have hc0 : 0 < ‖c‖ := lt_trans zero_lt_one hc
  have hc' : c ≠ 0 := norm_pos_iff.mp hc0
  have hxa : 0 ≤ x a := apply_nonneg x.toMulRingSeminorm a
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (inv_pos.mpr hc0)
    ((div_lt_one hr).mpr hxr)
  obtain ⟨m, hm1, hm2⟩ := exists_mem_Ico_zpow (pow_pos hr n) hc
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hn
    exact absurd hn (not_lt.mpr (inv_le_one_of_one_le₀ hc.le))
  have hcm : 0 < ‖c‖ ^ m := zpow_pos hc0 m
  have hval : ∀ y : BanachSpectrum P,
      y (algebraMap K P (c ^ (-m)) * a ^ n) = (‖c‖ ^ m)⁻¹ * y a ^ n := by
    intro y
    rw [map_mul, BanachSpectrum.algebraMap_apply, map_pow, norm_zpow, zpow_neg]
  refine ⟨algebraMap K P (c ^ (-m)) * a ^ n, ?_, ?_⟩
  · rw [hval, inv_mul_lt_one₀ hcm]
    have h1 : x a ^ n * ‖c‖ < r ^ n := by
      rw [div_pow, div_lt_iff₀ (pow_pos hr n)] at hn
      calc x a ^ n * ‖c‖ = ‖c‖ * x a ^ n := mul_comm _ _
        _ < ‖c‖ * (‖c‖⁻¹ * r ^ n) := mul_lt_mul_of_pos_left hn hc0
        _ = r ^ n := by field_simp
    have h2 : r ^ n < ‖c‖ ^ m * ‖c‖ := by
      rwa [← zpow_add_one₀ hc0.ne']
    exact lt_of_mul_lt_mul_right (h1.trans h2) hc0.le
  · intro y hy
    rw [hval, inv_mul_le_one₀ hcm] at hy
    exact (pow_le_pow_iff_left₀ (apply_nonneg y.toMulRingSeminorm a) hr.le hn0).mp
      (hy.trans hm1)

omit [CompleteSpace K] in
/-- A strict lower bound at a point can be replaced by a unit-radius lower
bound on a monomial `c⁻ᵐ bⁿ` which is still strict at the point and implies
the original bound everywhere. -/
theorem exists_lower_unit_bound {c : K} (hc : 1 < ‖c‖) (x : BanachSpectrum P)
    (b : P) {q : ℝ} (hq : 0 < q) (hxq : q < x b) :
    ∃ f : P, 1 < x f ∧ ∀ y : BanachSpectrum P, 1 ≤ y f → q ≤ y b := by
  have hc0 : 0 < ‖c‖ := lt_trans zero_lt_one hc
  have hxb : 0 < x b := hq.trans hxq
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (inv_pos.mpr hc0)
    ((div_lt_one hxb).mpr hxq)
  obtain ⟨m, hm1, hm2⟩ := exists_mem_Ico_zpow (pow_pos hq n) hc
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hn
    exact absurd hn (not_lt.mpr (inv_le_one_of_one_le₀ hc.le))
  have hcm : 0 < ‖c‖ ^ (m + 1) := zpow_pos hc0 _
  have hval : ∀ y : BanachSpectrum P,
      y (algebraMap K P (c ^ (-(m + 1))) * b ^ n) =
        (‖c‖ ^ (m + 1))⁻¹ * y b ^ n := by
    intro y
    rw [map_mul, BanachSpectrum.algebraMap_apply, map_pow, norm_zpow, zpow_neg]
  refine ⟨algebraMap K P (c ^ (-(m + 1))) * b ^ n, ?_, ?_⟩
  · rw [hval, lt_inv_mul_iff₀ hcm, mul_one]
    have h1 : ‖c‖ * q ^ n < x b ^ n := by
      rw [div_pow, div_lt_iff₀ (pow_pos hxb n)] at hn
      calc ‖c‖ * q ^ n < ‖c‖ * (‖c‖⁻¹ * x b ^ n) := mul_lt_mul_of_pos_left hn hc0
        _ = x b ^ n := by field_simp
    have h2 : ‖c‖ ^ (m + 1) ≤ ‖c‖ * q ^ n := by
      rw [zpow_add_one₀ hc0.ne', mul_comm]
      exact mul_le_mul_of_nonneg_left hm1 hc0.le
    exact h2.trans_lt h1
  · intro y hy
    rw [hval, le_inv_mul_iff₀ hcm, mul_one] at hy
    exact (pow_le_pow_iff_left₀ hq.le (apply_nonneg y.toMulRingSeminorm b) hn0).mp
      (hm2.le.trans hy)

/-- Over a complete field with an element of norm greater than one, the loci of
rational data form a neighbourhood basis of every point of the spectrum. -/
theorem exists_locus_mem_nhds_subset (hK : ∃ c : K, 1 < ‖c‖) (x : BanachSpectrum P)
    {V : Set (BanachSpectrum P)} (hV : V ∈ 𝓝 x) :
    ∃ d : RationalData K P, d.locus ∈ 𝓝 x ∧ d.locus ⊆ V := by
  classical
  obtain ⟨c, hc⟩ := hK
  obtain ⟨s, t, r, q, hrpos, hqpos, hr, hq, -, hsub⟩ :=
    BanachSpectrum.exists_finite_laurent_neighborhood x V hV
  choose fU hfUx hfU using fun i : s => exists_upper_unit_bound hc x i.val (hrpos i) (hr i)
  choose fL hfLx hfL using fun j : t => exists_lower_unit_bound hc x j.val (hqpos j) (hq j)
  let d : RationalData K P :=
    listInter (s.attach.toList.map (fun i => laurentUpper (fU i)) ++
      t.attach.toList.map (fun j => laurentLower (fL j)))
  have hmem : ∀ y : BanachSpectrum P,
      y ∈ d.locus ↔ (∀ i, y (fU i) ≤ 1) ∧ ∀ j, 1 ≤ y (fL j) := by
    intro y
    simp only [d, mem_locus_listInter, List.mem_append, or_imp, forall_and,
      List.forall_mem_map, Finset.mem_toList, Finset.mem_attach, true_implies,
      mem_locus_laurentUpper, mem_locus_laurentLower]
  refine ⟨d, ?_, ?_⟩
  · have hset : d.locus = (⋂ i, {y : BanachSpectrum P | y (fU i) ≤ 1}) ∩
        ⋂ j, {y : BanachSpectrum P | 1 ≤ y (fL j)} := by
      ext y
      rw [hmem]
      simp
    rw [hset]
    apply Filter.inter_mem
    · apply Filter.iInter_mem.mpr
      intro i
      exact (BanachSpectrum.evaluation (fU i)).continuous.continuousAt
        (Iic_mem_nhds (hfUx i))
    · apply Filter.iInter_mem.mpr
      intro j
      exact (BanachSpectrum.evaluation (fL j)).continuous.continuousAt
        (Ici_mem_nhds (hfLx j))
  · intro y hy
    rw [hmem] at hy
    exact hsub ⟨fun i => hfU i y (hy.1 i), fun j => hfL j y (hy.2 j)⟩

end Langlands.Analytic.StrictTestDomain.RationalData
