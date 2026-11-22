import Langlands.Global.LeftCosetImageMajorant
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Exp

/-! # An exponential height moment on a discrete left quotient -/

noncomputable section
set_option autoImplicit false

universe u v

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal Pointwise

namespace Langlands.Global.LeftCosetSpace

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  {ν : Measure G} [ν.IsMulLeftInvariant]

omit [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G] in
private theorem isCompact_set_pow {D : Set G} (hD : IsCompact D) (n : ℕ) : IsCompact (D ^ n) := by
  induction n with
  | zero => simpa only [pow_zero, ← Set.singleton_one] using isCompact_singleton
  | succ n ih => rw [pow_succ]; exact ih.mul hD

omit [T2Space G] [LocallyCompactSpace G] in
/-- A compact identity neighborhood has volumes of its powers bounded by a geometric
progression, by translating a finite cover of its square. -/
private theorem exists_measure_set_pow_le {D : Set G} (hD : IsCompact D) (hD₁ : D ∈ 𝓝 (1 : G)) :
    ∃ a : ℝ≥0, 1 ≤ a ∧ ∀ n : ℕ, ν (D ^ (n + 1)) ≤ (a : ℝ≥0∞) ^ n * ν D := by
  let U (g : G) : Set G := g • interior D
  have hU (g : G) : IsOpen (U g) := isOpen_interior.smul g
  have hcover : D ^ 2 ⊆ ⋃ g, U g := by
    intro x _
    have h1 : (1 : G) ∈ interior D := mem_interior_iff_mem_nhds.mpr hD₁
    exact Set.mem_iUnion.mpr ⟨x, ⟨1, h1, mul_one x⟩⟩
  obtain ⟨I, hI⟩ := (hD.mul hD).elim_finite_subcover U hU (by simpa only [pow_two] using hcover)
  let a : ℝ≥0 := max 1 I.card
  refine ⟨a, le_max_left _ _, fun n => ?_⟩
  induction n with
  | zero => simp
  | succ n ih =>
    have hpre : D ^ (n + 2) ⊆ ⋃ g ∈ I, g • (D ^ (n + 1)) := by
      rw [show n + 2 = 2 + n by omega, pow_add]
      rintro x ⟨y, hy, z, hz, rfl⟩
      obtain ⟨g, hg, hgy⟩ := Set.mem_iUnion₂.mp (hI (by simpa only [pow_two] using hy))
      obtain ⟨b, hb, rfl⟩ := hgy
      refine Set.mem_iUnion₂.mpr ⟨g, hg, b * z, ?_, mul_assoc g b z |>.symm⟩
      rw [pow_succ']
      exact Set.mul_mem_mul (interior_subset hb) hz
    calc
      ν (D ^ ((n + 1) + 1)) ≤ ν (⋃ g ∈ I, g • (D ^ (n + 1))) := measure_mono hpre
      _ ≤ ∑ g ∈ I, ν (g • (D ^ (n + 1))) := measure_biUnion_finset_le I _
      _ = (I.card : ℝ≥0∞) * ν (D ^ (n + 1)) := by simp only [measure_smul, Finset.sum_const, nsmul_eq_mul]
      _ ≤ (a : ℝ≥0∞) * ((a : ℝ≥0∞) ^ n * ν D) := by
        have hcard : (I.card : ℝ≥0) ≤ a := le_max_right _ _
        exact mul_le_mul' (by exact_mod_cast hcard) ih
      _ = (a : ℝ≥0∞) ^ (n + 1) * ν D := by rw [pow_succ', mul_assoc]

/-- If a discrete left quotient has representatives given by compact factors on
both sides of a continuous multiplicative section of a finite-dimensional
real height coordinate, some decaying exponential of the coordinate norm is
integrable against the quotient measure. -/
def LeftCosetExponentialHeightMomentStatement : Prop :=
  ∀ (Γ : Subgroup G) (hΓ : IsDiscrete (Γ : Set G)) [SecondCountableTopology G]
    (V : Type v) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (a : Multiplicative V →ₜ* G) (h : LeftCosetSpace Γ → V),
    Measurable (fun z => ‖h z‖) →
    ∀ (Ω K : Set G), IsCompact Ω → IsCompact K →
    (∀ z, ∃ p ∈ Ω, ∃ k ∈ K, mk Γ (p * a (Multiplicative.ofAdd (h z)) * k) = z) →
    IsFiniteMeasureOnCompacts ν →
    ∃ c : ℝ, 0 < c ∧
      ∀ r : ℝ, c ≤ r → (∫⁻ z, ENNReal.ofReal (Real.exp (-r * ‖h z‖))
        ∂discreteQuotientMeasure Γ hΓ ν) < ∞

theorem leftCosetExponentialHeightMoment : LeftCosetExponentialHeightMomentStatement.{u,v} (ν := ν) := by
  intro Γ hΓ _ V _ _ _ a h hh Ω K hΩ hK hrep hFinite
  let : Countable Γ := countable_of_isDiscrete Γ hΓ
  let : IsFiniteMeasureOnCompacts ν := hFinite
  let : ProperSpace V := FiniteDimensional.proper ℝ V
  obtain ⟨D₀, hD₀, hD₀₁⟩ := exists_compact_mem_nhds (1 : G)
  let U := a '' (Multiplicative.ofAdd '' Metric.closedBall (0 : V) 1)
  let D := D₀ ∪ (Ω ∪ K) ∪ U
  have hD : IsCompact D := (hD₀.union (hΩ.union hK)).union
    (((isCompact_closedBall _ _).image continuous_id).image a.continuous)
  have hD₁ : D ∈ 𝓝 (1 : G) := mem_of_superset hD₀₁ fun _ hx => Or.inl (Or.inl hx)
  have hΩD : Ω ⊆ D := fun _ hx => Or.inl (Or.inr (Or.inl hx))
  have hKD : K ⊆ D := fun _ hx => Or.inl (Or.inr (Or.inr hx))
  have hVD (x : V) (hx : ‖x‖ ≤ 1) : a (Multiplicative.ofAdd x) ∈ D :=
    Or.inr ⟨_, ⟨x, by simpa only [Metric.mem_closedBall, dist_zero_right] using hx, rfl⟩, rfl⟩
  obtain ⟨A, hA, hpow⟩ := exists_measure_set_pow_le (ν := ν) hD hD₁
  let Q := discreteQuotientMeasure Γ hΓ ν
  let S (n : ℕ) := {z : LeftCosetSpace Γ | (n : ℝ) ≤ ‖h z‖ ∧ ‖h z‖ ≤ (n : ℝ) + 1}
  have hS (n : ℕ) : MeasurableSet (S n) :=
    (measurableSet_le measurable_const hh).inter (measurableSet_le hh measurable_const)
  have hAll : ⋃ n, S n = Set.univ := by
    refine Set.eq_univ_of_forall fun z => Set.mem_iUnion.mpr ⟨⌊‖h z‖⌋₊, ?_⟩
    exact ⟨Nat.floor_le (norm_nonneg _), (Nat.lt_floor_add_one _).le⟩
  have himage (n : ℕ) : S n ⊆ mk Γ '' (D ^ (n + 3)) := by
    intro z hz
    obtain ⟨p, hp, k, hk, hEq⟩ := hrep z
    let y := ((n : ℝ) + 1)⁻¹ • h z
    have hn : 0 < (n : ℝ) + 1 := by positivity
    have hy : ‖y‖ ≤ 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn)]
      exact (inv_mul_le_one₀ hn).mpr hz.2
    have heq : (n + 1) • y = h z := by
      rw [← Nat.cast_smul_eq_nsmul ℝ, Nat.cast_add, Nat.cast_one, smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
    have hP : a (Multiplicative.ofAdd (h z)) = a (Multiplicative.ofAdd y) ^ (n + 1) := by
      rw [← map_pow]
      exact congrArg a (congrArg Multiplicative.ofAdd heq).symm
    refine ⟨_, ?_, hEq⟩
    rw [hP, show n + 3 = 1 + (n + 1) + 1 by omega, pow_add, pow_add, pow_one]
    exact Set.mul_mem_mul (Set.mul_mem_mul (hΩD hp) (Set.pow_mem_pow (hVD y hy))) (hKD hk)
  have hvol (n : ℕ) : Q (S n) ≤ (A : ℝ≥0∞) ^ (n + 2) * ν D := by
    have hM := measurableSet_mk_image Γ (isCompact_set_pow hD (n + 3))
    exact (measure_mono (himage n)).trans ((quotientMeasure_mk_image_le Γ ν
      (isFundamentalDomain Γ hΓ ν) hM).trans (hpow (n + 2)))
  have hA₀ : 0 < (A : ℝ) := lt_of_lt_of_le zero_lt_one (by exact_mod_cast hA)
  let c := Real.log (A : ℝ) + 1
  have hc : 0 < c := by
    have hh := Real.log_nonneg (show 1 ≤ (A : ℝ) by exact_mod_cast hA)
    dsimp [c]
    linarith
  let f (z : LeftCosetSpace Γ) := ENNReal.ofReal (Real.exp (-c * ‖h z‖))
  let q := ENNReal.ofReal (Real.exp (-1))
  have hq : q < 1 := by
    rw [← ENNReal.ofReal_one, ENNReal.ofReal_lt_ofReal_iff zero_lt_one]
    simpa only [← Real.exp_zero, Real.exp_lt_exp] using (show (-1 : ℝ) < 0 by norm_num)
  let M := (A : ℝ≥0∞) ^ (2 : ℕ) * ν D
  have hM : M ≠ ∞ := ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.coe_ne_top) hD.measure_lt_top.ne
  have hGeom (n : ℕ) : ENNReal.ofReal (Real.exp (-c * n)) * ((A : ℝ≥0∞) ^ (n + 2) * ν D) =
      M * q ^ n := by
    rw [mul_comm (-c) (n : ℝ), Real.exp_nat_mul, ENNReal.ofReal_pow (Real.exp_nonneg _), pow_add]
    dsimp only [M, q]
    calc
      _ = (A : ℝ≥0∞) ^ (2 : ℕ) * ν D * (ENNReal.ofReal (Real.exp (-c)) * (A : ℝ≥0∞)) ^ n := by
        rw [mul_pow]
        simp only [mul_assoc, mul_left_comm, mul_comm]
      _ = _ := by
        congr 2
        dsimp only [c]
        rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (Real.exp_nonneg _),
          neg_add, Real.exp_add, Real.exp_neg (Real.log _), Real.exp_log hA₀]
        field_simp
  have hI (n : ℕ) : (∫⁻ z in S n, f z ∂Q) ≤ M * q ^ n := by
    have hx : ∀ᵐ z ∂Q.restrict (S n), f z ≤ ENNReal.ofReal (Real.exp (-c * n)) :=
      (ae_restrict_mem (hS n)).mono fun z hz => ENNReal.ofReal_le_ofReal
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hz.1 (neg_nonpos.mpr hc.le)))
    calc
      _ ≤ ∫⁻ _ in S n, ENNReal.ofReal (Real.exp (-c * n)) ∂Q := lintegral_mono_ae hx
      _ = ENNReal.ofReal (Real.exp (-c * n)) * Q (S n) := by
        rw [lintegral_const, Measure.restrict_apply_univ]
      _ ≤ ENNReal.ofReal (Real.exp (-c * n)) * ((A : ℝ≥0∞) ^ (n + 2) * ν D) := by
        gcongr
        exact hvol n
      _ = _ := hGeom n
  have hInt : (∫⁻ z, f z ∂Q) < ∞ := by
    rw [← Measure.restrict_univ (μ := Q), ← hAll]
    refine (lintegral_iUnion_le S f).trans_lt ?_
    refine (ENNReal.tsum_le_tsum hI).trans_lt ?_
    rw [ENNReal.tsum_mul_left]
    exact ENNReal.mul_lt_top hM.lt_top (tsum_geometric_lt_top.mpr hq)
  refine ⟨c, hc, fun r hr => ?_⟩
  exact (lintegral_mono fun z => ENNReal.ofReal_le_ofReal
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (neg_le_neg hr) (norm_nonneg _)))).trans_lt hInt

end Langlands.Global.LeftCosetSpace
