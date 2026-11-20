import Langlands.Analysis.TraceClassKernelDiagonalCells
import Mathlib.Analysis.Convex.Integral
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Prod

/-!
# Diagonal identification from square-cell integral identities

On a finite Borel measure space, square-cell averages identify the diagonal of a kernel
with the diagonal of a square-summable rank-one expansion. No uniqueness assertion
for the product-measure kernel is needed.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ComplexConjugate

namespace Langlands.Analysis.OperatorIdeals.KernelDiagonal

variable {X ι : Type*} [MeasurableSpace X]

/-- The nonnegative majorant of a rank-one product, from the arithmetic mean inequality. -/
def energy (a b : ℂ) : ℝ := (‖a‖ ^ 2 + ‖b‖ ^ 2) / 2

lemma energy_nonneg (a b : ℂ) : 0 ≤ energy a b := by
  unfold energy
  positivity

lemma norm_mul_conj_le_energy (a b : ℂ) : ‖a * conj b‖ ≤ energy a b := by
  rw [norm_mul, Complex.norm_conj, energy, le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
  simpa [mul_assoc, mul_comm, mul_left_comm] using two_mul_le_add_sq ‖a‖ ‖b‖

lemma exists_nhds_basis_seq [TopologicalSpace X] [SecondCountableTopology X] [BorelSpace X] :
    ∃ B : ℕ → Set X, (∀ n, MeasurableSet (B n)) ∧
      (∀ x, ∀ U ∈ 𝓝 x, ∃ n, x ∈ B n ∧ B n ⊆ U) := by
  obtain ⟨b, hbc, -, hb⟩ := TopologicalSpace.exists_countable_basis (α := X)
  obtain ⟨B, hB⟩ := (hbc.insert ∅).exists_eq_range (Set.insert_nonempty _ _)
  refine ⟨B, fun n => ?_, fun x U hU => ?_⟩
  · have hn : B n ∈ insert ∅ b := hB ▸ Set.mem_range_self n
    rcases Set.mem_insert_iff.1 hn with he | he
    · simp [he]
    · exact (hb.isOpen he).measurableSet
  · obtain ⟨V, hV, hxV, hVU⟩ := hb.mem_nhds_iff.1 hU
    obtain ⟨n, rfl⟩ : V ∈ Set.range B := hB ▸ Set.mem_insert_of_mem _ hV
    exact ⟨n, hxV, hVU⟩

section Series

variable {μ ν : Measure X} {E : Type*} [NormedAddCommGroup E] {f : ι → X → E}

lemma summable_integral_norm_mono_measure (hν : ν ≤ μ) (hf : ∀ i, Integrable (f i) μ)
    (hs : Summable fun i => ∫ x, ‖f i x‖ ∂μ) : Summable fun i => ∫ x, ‖f i x‖ ∂ν :=
  hs.of_nonneg_of_le (fun _ => integral_nonneg fun _ => norm_nonneg _)
    (fun i => integral_mono_measure hν (Eventually.of_forall fun _ => norm_nonneg _) (hf i).norm)

private lemma tsum_lintegral_enorm_ne_top (hf : ∀ i, Integrable (f i) μ)
    (hs : Summable fun i => ∫ x, ‖f i x‖ ∂μ) : (∑' i, ∫⁻ x, ‖f i x‖ₑ ∂μ) ≠ ⊤ := by
  have h (i : ι) : ∫⁻ x, ‖f i x‖ₑ ∂μ = ‖∫ x, ‖f i x‖ ∂μ‖ₑ := by
    rw [Real.enorm_of_nonneg (integral_nonneg fun _ => norm_nonneg _),
      ofReal_integral_norm_eq_lintegral_enorm (hf i)]
  rw [funext h]
  exact tsum_enorm_ne_top_iff_summable_norm.2 hs.abs

variable [Countable ι]

lemma integrable_tsum_of_summable_integral_norm [NormedSpace ℝ E] [CompleteSpace E]
    (hf : ∀ i, Integrable (f i) μ) (hs : Summable fun i => ∫ x, ‖f i x‖ ∂μ) :
    Integrable (fun x => ∑' i, f i x) μ := by
  refine ⟨AEStronglyMeasurable.tsum (fun i => (hf i).aestronglyMeasurable), ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  calc
    _ ≤ ∫⁻ x, ∑' i, ‖f i x‖ₑ ∂μ := lintegral_mono fun _ => enorm_tsum_le_tsum_enorm
    _ = ∑' i, ∫⁻ x, ‖f i x‖ₑ ∂μ := lintegral_tsum fun i => (hf i).aestronglyMeasurable.enorm
    _ < ⊤ := (tsum_lintegral_enorm_ne_top hf hs).lt_top

private lemma ae_summable_norm (hf : ∀ i, Integrable (f i) μ)
    (hs : Summable fun i => ∫ x, ‖f i x‖ ∂μ) : ∀ᵐ x ∂μ, Summable fun i => ‖f i x‖ := by
  have hm (i : ι) := (hf i).aestronglyMeasurable.enorm
  have ht := ae_lt_top' (AEMeasurable.tsum hm) (by
    rw [lintegral_tsum hm]
    exact tsum_lintegral_enorm_ne_top hf hs)
  exact ht.mono fun _ hx => tsum_enorm_ne_top_iff_summable_norm.1 hx.ne

end Series

section Averages

variable {ν : Measure X} [IsFiniteMeasure ν]

private lemma norm_setAverage_sq_le {f : X → ℂ} {A : Set X} (hA : ν A ≠ 0)
    (hf : Integrable f ν) (hf₂ : Integrable (fun x => ‖f x‖ ^ 2) ν) :
    ‖⨍ x in A, f x ∂ν‖ ^ 2 ≤ ⨍ x in A, ‖f x‖ ^ 2 ∂ν := by
  have hc : ConvexOn ℝ (Set.univ : Set ℂ) (fun z => ‖z‖ ^ 2) :=
    (convexOn_norm convex_univ).pow (fun _ _ => norm_nonneg _) 2
  exact hc.map_set_average_le (continuous_norm.pow 2).continuousOn isClosed_univ hA
    (measure_ne_top _ _) (Eventually.of_forall fun _ => Set.mem_univ _) hf.integrableOn
    hf₂.integrableOn

private lemma norm_mul_conj_setAverage_le {a b : X → ℂ} {A : Set X} (hA : ν A ≠ 0)
    (ha : Integrable a ν) (hb : Integrable b ν)
    (ha₂ : Integrable (fun x => ‖a x‖ ^ 2) ν) (hb₂ : Integrable (fun x => ‖b x‖ ^ 2) ν) :
    ‖(⨍ x in A, a x ∂ν) * conj (⨍ x in A, b x ∂ν)‖ ≤ ⨍ x in A, energy (a x) (b x) ∂ν := by
  refine (norm_mul_conj_le_energy _ _).trans ?_
  have h := add_le_add (norm_setAverage_sq_le hA ha ha₂) (norm_setAverage_sq_le hA hb hb₂)
  change (‖⨍ x in A, a x ∂ν‖ ^ 2 + ‖⨍ x in A, b x ∂ν‖ ^ 2) / 2 ≤
    ⨍ x in A, (‖a x‖ ^ 2 + ‖b x‖ ^ 2) / 2 ∂ν
  simp only [setAverage_eq, smul_eq_mul] at h ⊢
  rw [integral_div, integral_add ha₂.integrableOn hb₂.integrableOn]
  linarith only [h]

private lemma setAverage_prod_eq_tsum {K : X → X → ℂ} {a b : ι → X → ℂ} {A : Set X}
    (h : ∫ p in A ×ˢ A, Function.uncurry K p ∂(ν.prod ν) =
      ∑' i, (∫ y in A, a i y ∂ν) * conj (∫ y in A, b i y ∂ν)) :
    ⨍ p in A ×ˢ A, Function.uncurry K p ∂(ν.prod ν) =
      ∑' i, (⨍ y in A, a i y ∂ν) * conj (⨍ y in A, b i y ∂ν) := by
  simp only [setAverage_eq, measureReal_prod_prod, h, Complex.real_smul, map_mul,
    Complex.conj_ofReal, ← tsum_mul_left, mul_inv, Complex.ofReal_mul]
  exact tsum_congr fun i => by ring

private lemma tendsto_setAverage_prod_cell [TopologicalSpace X] {B : ℕ → Set X} {x : X}
    (hBn : ∀ U ∈ 𝓝 x, ∃ n, x ∈ B n ∧ B n ⊆ U) (hx : ∀ m, ν (cell B m x) ≠ 0)
    {k : X × X → ℂ} (hk : Integrable k (ν.prod ν)) (hc : ContinuousAt k (x, x)) :
    Tendsto (fun m => ⨍ p in cell B m x ×ˢ cell B m x, k p ∂(ν.prod ν)) atTop (𝓝 (k (x, x))) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hV : {p | dist (k p) (k (x, x)) < ε / 2} ∈ 𝓝 (x, x) :=
    Metric.tendsto_nhds.1 hc (ε / 2) (by positivity)
  rw [nhds_prod_eq] at hV
  obtain ⟨U, hU, hUV⟩ := Filter.mem_prod_self_iff.1 hV
  obtain ⟨n, hxn, hn⟩ := hBn U hU
  filter_upwards [eventually_gt_atTop n] with m hm
  let A := cell B m x ×ˢ cell B m x
  have hA : ν.prod ν A ≠ 0 := by
    rw [show A = cell B m x ×ˢ cell B m x from rfl, Measure.prod_prod]
    exact mul_ne_zero (hx m) (hx m)
  change dist (⨍ p in A, k p ∂(ν.prod ν)) (k (x, x)) < ε
  apply lt_of_le_of_lt _ (half_lt_self hε)
  rw [dist_eq_norm, ← setAverage_const hA (measure_ne_top _ _) (k (x, x)),
    ← setAverage_sub hk.integrableOn (integrable_const _), setAverage_eq, norm_smul,
    Real.norm_of_nonneg (inv_nonneg.2 measureReal_nonneg)]
  have hle : ∀ p ∈ A, ‖k p - k (x, x)‖ ≤ ε / 2 := by
    intro p hp
    have hs := (cell_subset hm hxn).trans hn
    have hp' : dist (k p) (k (x, x)) < ε / 2 :=
      hUV (show p ∈ U ×ˢ U from ⟨hs hp.1, hs hp.2⟩)
    rw [dist_eq_norm] at hp'
    exact hp'.le
  have he : (ν.prod ν).real A ≠ 0 := (measureReal_ne_zero_iff (measure_ne_top _ _)).2 hA
  calc
    _ ≤ ((ν.prod ν).real A)⁻¹ * (ε / 2 * (ν.prod ν).real A) :=
      mul_le_mul_of_nonneg_left (norm_setIntegral_le_of_norm_le_const (measure_lt_top _ _) hle)
        (inv_nonneg.2 measureReal_nonneg)
    _ = ε / 2 := by rw [mul_left_comm, inv_mul_cancel₀ he, mul_one]

/-- Use only the square-set integral identities to identify the diagonal a.e. -/
theorem ae_eq_diagonal_tsum [TopologicalSpace X] [SecondCountableTopology X] [BorelSpace X]
    [Countable ι] {K : X → X → ℂ} {a b : ι → X → ℂ}
    (ha : ∀ i, MemLp (a i) 2 ν) (hb : ∀ i, MemLp (b i) 2 ν)
    (hW : Summable fun i => ∫ x, ‖energy (a i x) (b i x)‖ ∂ν)
    (hK : Integrable (Function.uncurry K) (ν.prod ν))
    (hcell : ∀ A : Set X, MeasurableSet A → ∫ p in A ×ˢ A, Function.uncurry K p ∂(ν.prod ν) =
      ∑' i, (∫ y in A, a i y ∂ν) * conj (∫ y in A, b i y ∂ν))
    (hc : ∀ᵐ x ∂ν, ContinuousAt (Function.uncurry K) (x, x)) :
    ∀ᵐ x ∂ν, K x x = ∑' i, a i x * conj (b i x) := by
  classical
  let w (i : ι) (y : X) := energy (a i y) (b i y)
  have hw₀ i y : 0 ≤ w i y := energy_nonneg _ _
  have ha₂ i := (memLp_two_iff_integrable_sq_norm (ha i).aestronglyMeasurable).1 (ha i)
  have hb₂ i := (memLp_two_iff_integrable_sq_norm (hb i).aestronglyMeasurable).1 (hb i)
  have hw (i : ι) : Integrable (w i) ν := ((ha₂ i).add (hb₂ i)).div_const 2
  let tail (F : Finset ι) (y : X) := ∑' i : ↥(F : Set ι)ᶜ, w i y
  have ht (F : Finset ι) : Integrable (tail F) ν :=
    integrable_tsum_of_summable_integral_norm (fun i => hw i) (hW.subtype _)
  obtain ⟨B, hB, hBn⟩ := exists_nhds_basis_seq (X := X)
  have haL i := (ha i).integrable (by norm_num)
  have hbL i := (hb i).integrable (by norm_num)
  have hta := ae_all_iff.2 fun i => ae_tendsto_setAverage_cell_complex ν hB hBn (haL i)
  have htb := ae_all_iff.2 fun i => ae_tendsto_setAverage_cell_complex ν hB hBn (hbL i)
  have htt := ae_all_iff.2 fun F => ae_tendsto_setAverage_cell ν hB hBn (ht F)
  filter_upwards [hc, ae_measure_cell_ne_zero (B := B) ν, hta, htb, htt,
    ae_summable_norm hw hW] with x hx hx₀ hxa hxb hxt hxw
  have hws : Summable fun i => w i x := hxw.congr (fun i => Real.norm_of_nonneg (hw₀ i x))
  have hsum : Summable fun i => a i x * conj (b i x) :=
    hws.of_norm_bounded fun i => norm_mul_conj_le_energy _ _
  have hlim := tendsto_setAverage_prod_cell (hBn x) hx₀ hK hx
  have htail (F : Finset ι) : ‖K x x - ∑ i ∈ F, a i x * conj (b i x)‖ ≤ tail F x := by
    let v (m : ℕ) (i : ι) := (⨍ y in cell B m x, a i y ∂ν) * conj (⨍ y in cell B m x, b i y ∂ν)
    have hv (i : ι) : Tendsto (fun m => v m i) atTop (𝓝 (a i x * conj (b i x))) :=
      (hxa i).mul ((Complex.continuous_conj.tendsto _).comp (hxb i))
    have hfin : Tendsto (fun m => ∑ i ∈ F, v m i) atTop (𝓝 (∑ i ∈ F, a i x * conj (b i x))) :=
      tendsto_finsetSum F (fun i _ => hv i)
    refine le_of_tendsto_of_tendsto' ((hlim.sub hfin).norm) (hxt F) (fun m => ?_)
    let A := cell B m x
    let e (i : ι) := ⨍ y in A, w i y ∂ν
    have hle (i : ι) : ‖v m i‖ ≤ e i := norm_mul_conj_setAverage_le (hx₀ m)
      (haL i) (hbL i) (ha₂ i) (hb₂ i)
    have hi := summable_integral_norm_mono_measure (ν := ν.restrict A) Measure.restrict_le_self hw hW
    have he : Summable e := by
      simpa only [e, setAverage_eq, smul_eq_mul, Real.norm_of_nonneg (hw₀ _ _)] using
        hi.mul_left (ν.real A)⁻¹
    have hvs : Summable (v m) := he.of_norm_bounded hle
    have htail' : ∑' i : ↥(F : Set ι)ᶜ, e i = ⨍ y in A, tail F y ∂ν := by
      simp only [e, setAverage_eq, smul_eq_mul, tsum_mul_left, tail]
      rw [integral_tsum_of_summable_integral_norm (μ := ν.restrict A)
        (F := fun i : ↥(F : Set ι)ᶜ => w i) (fun i => (hw i).integrableOn) (hi.subtype _)]
    rw [setAverage_prod_eq_tsum (hcell A (measurableSet_cell hB m x)),
      show (∑' i, (⨍ y in A, a i y ∂ν) * conj (⨍ y in A, b i y ∂ν)) = ∑' i, v m i from rfl,
      ← hvs.sum_add_tsum_compl (s := F), add_sub_cancel_left, ← htail']
    exact tsum_of_norm_bounded (he.subtype (F : Set ι)ᶜ).hasSum (fun i => hle i)
  have hzero : ‖K x x - ∑' i, a i x * conj (b i x)‖ ≤ 0 :=
    le_of_tendsto_of_tendsto' ((tendsto_const_nhds.sub hsum.hasSum).norm)
      (tendsto_tsum_compl_atTop_zero (fun i => w i x)) htail
  exact sub_eq_zero.1 (norm_le_zero_iff.1 hzero)

end Averages

end Langlands.Analysis.OperatorIdeals.KernelDiagonal
