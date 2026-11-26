import Langlands.Global.AdelicLocalFinitenessChamberSlabs
import Langlands.Global.AdelicLocalFinitenessChamberWeights

/-! # From orthant estimates to the Siegel weight

The Siegel weight `exp(-2 (∑_β ra_β x_β + ∑_j rb_j |y_j|))` on the region where all root
coordinates exceed their thresholds is dominated by the sum over the central orthants `ε` of the
orthant weights restricted to their positive regions, and on each positive region the orthant
weight is at most `exp(4 ∑_j rb_j)` times the Siegel weight. Hence slab estimates for the orthant
weights give an estimate for the Siegel weight (Bernstein–Lapid §7.7).
-/

noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false

open MeasureTheory Set
open scoped ENNReal NNReal

namespace Langlands.Global.StandardConstantTerm

open Langlands.Global.AdelicSiegelFactors

variable {X D : Type*} [Fintype D] {r : ℕ}

/-- The region where all root coordinates exceed their thresholds. -/
def siegelRegion (τ : D → ℝ) : Set ((D → ℝ) × (Fin r → ℝ)) := {x | ∀ β, τ β < x.1 β}

/-- The Siegel weight `exp(-2 localFinitenessLogWeight ra rb x)` on `siegelRegion τ`, zero
elsewhere, for the coordinate map `c`. -/
def siegelWeight (c : X → (D → ℝ) × (Fin r → ℝ)) (ra : D → ℝ) (rb : Fin r → ℝ) (τ : D → ℝ)
    (g : X) : ℝ≥0∞ :=
  (siegelRegion τ).indicator
    (fun x => ENNReal.ofReal (Real.exp (-2 * localFinitenessLogWeight ra rb x))) (c g)

/-- The positive region of the orthant heights. -/
def orthantPos (c : X → (D → ℝ) × (Fin r → ℝ)) (τ : D → ℝ) (J : D → Prop) (ε : Fin r → Bool) :
    Set X :=
  {g | ∀ k, 0 < orthantHeight c τ J ε k g}

/-- The orthant of a central point: the signs of its central coordinates. -/
def orthantOf (y : Fin r → ℝ) : Fin r → Bool := fun j => decide (0 ≤ y j)

theorem orthantCoord_orthantOf (y : Fin r → ℝ) (j : Fin r) :
    orthantCoord (orthantOf y) j (y j) = |y j| := by
  unfold orthantCoord orthantOf
  by_cases h : 0 ≤ y j
  · simp [h, abs_of_nonneg h]
  · simp [h, abs_of_neg (lt_of_not_ge h)]

/-- The Siegel weight is at most the sum of the orthant weights on their positive regions. -/
theorem siegelWeight_le_sum (c : X → (D → ℝ) × (Fin r → ℝ)) (ra : D → ℝ) (rb : Fin r → ℝ)
    (τ : D → ℝ) (J : D → Prop) (g : X) :
    siegelWeight c ra rb τ g ≤
      ∑ ε : Fin r → Bool, (orthantPos c τ J ε).indicator (orthantWeight c ra rb τ J ε) g := by
  by_cases hg : c g ∈ siegelRegion τ
  · let ε₀ := orthantOf (c g).2
    have hpos : g ∈ orthantPos c τ J ε₀ := by
      rintro (β | j)
      · simp only [orthantHeight, Sum.elim_inl]
        exact sub_pos.mpr (hg β.1)
      · simp only [orthantHeight, Sum.elim_inr, ε₀, orthantCoord_orthantOf]
        positivity
    have hlevi : c g ∈ leviRegion τ J := fun β _ => hg β
    have heq : siegelWeight c ra rb τ g = orthantWeight c ra rb τ J ε₀ g := by
      unfold siegelWeight orthantWeight
      rw [indicator_of_mem hg, indicator_of_mem hlevi]
      congr 3
      unfold localFinitenessLogWeight orthantLogWeight
      congr 1
      exact Finset.sum_congr rfl fun j _ => by rw [orthantCoord_orthantOf]
    rw [heq]
    calc orthantWeight c ra rb τ J ε₀ g
        = (orthantPos c τ J ε₀).indicator (orthantWeight c ra rb τ J ε₀) g :=
          (indicator_of_mem hpos _).symm
      _ ≤ _ := Finset.single_le_sum (f := fun ε => (orthantPos c τ J ε).indicator
          (orthantWeight c ra rb τ J ε) g) (fun _ _ => zero_le) (Finset.mem_univ ε₀)
  · unfold siegelWeight
    rw [indicator_of_notMem hg]
    exact zero_le

/-- On its positive region, an orthant weight is at most `exp(4 ∑_j rb_j)` times the Siegel
weight, for nonnegative central rates. -/
theorem orthantWeight_le_siegelWeight (c : X → (D → ℝ) × (Fin r → ℝ)) (ra : D → ℝ)
    (rb : Fin r → ℝ) (hrb : ∀ j, 0 ≤ rb j) (τ : D → ℝ) (J : D → Prop) (ε : Fin r → Bool) (g : X) :
    (orthantPos c τ J ε).indicator (orthantWeight c ra rb τ J ε) g ≤
      ENNReal.ofReal (Real.exp (4 * ∑ j, rb j)) * siegelWeight c ra rb τ g := by
  by_cases hp : g ∈ orthantPos c τ J ε
  · rw [indicator_of_mem hp]
    unfold orthantWeight
    by_cases hl : c g ∈ leviRegion τ J
    · have hreg : c g ∈ siegelRegion τ := by
        intro β
        by_cases hβ : J β
        · exact hl β hβ
        · have := hp (Sum.inl ⟨β, hβ⟩)
          simp only [orthantHeight, Sum.elim_inl] at this
          linarith
      unfold siegelWeight
      rw [indicator_of_mem hl, indicator_of_mem hreg, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
        ← Real.exp_add]
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      have hcen (j : Fin r) : rb j * |(c g).2 j| ≤ rb j * orthantCoord ε j ((c g).2 j) + 2 * rb j := by
        have h := hp (Sum.inr j)
        simp only [orthantHeight, Sum.elim_inr] at h
        have h' : |(c g).2 j| ≤ orthantCoord ε j ((c g).2 j) + 2 := by
          unfold orthantCoord at h ⊢
          split_ifs at h ⊢
          · cases abs_cases ((c g).2 j) <;> linarith
          · cases abs_cases ((c g).2 j) <;> linarith
        nlinarith [hrb j]
      have hsum := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => hcen j
      rw [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
      unfold localFinitenessLogWeight orthantLogWeight
      linarith
    · rw [indicator_of_notMem hl]
      exact zero_le
  · rw [indicator_of_notMem hp]
    exact zero_le

section Measures

variable [MeasurableSpace X]

/-- The `L²` seminorm for a sum of two measures is at most the sum of the seminorms. -/
theorem eLpNorm_two_add_measure_le {f : X → ℂ} (hf : Measurable f) (μ μ' : Measure X) :
    eLpNorm f 2 (μ + μ') ≤ eLpNorm f 2 μ + eLpNorm f 2 μ' := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top
      hf.aestronglyMeasurable,
    eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top
      hf.aestronglyMeasurable,
    eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top
      hf.aestronglyMeasurable, lintegral_add_measure]
  exact ENNReal.rpow_add_le_add_rpow _ _ (by norm_num) (by norm_num)

/-- The `L²` seminorm for a finite sum of measures is at most the sum of the seminorms. -/
theorem eLpNorm_two_finset_sum_measure_le {ι : Type*} {f : X → ℂ} (hf : Measurable f)
    (s : Finset ι) (μ : ι → Measure X) :
    eLpNorm f 2 (∑ i ∈ s, μ i) ≤ ∑ i ∈ s, eLpNorm f 2 (μ i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (eLpNorm_two_add_measure_le hf _ _).trans (add_le_add le_rfl ih)

/-- Membership in `L²` for a finite sum of measures. -/
theorem memLp_two_finset_sum_measure {ι : Type*} {f : X → ℂ} (s : Finset ι) (μ : ι → Measure X)
    (h : ∀ i ∈ s, MemLp f 2 (μ i)) : MemLp f 2 (∑ i ∈ s, μ i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty]
    exact memLp_measure_zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact memLp_add_measure.mpr ⟨h a (Finset.mem_insert_self a s),
      ih fun i hi => h i (Finset.mem_insert_of_mem hi)⟩

theorem measurable_siegelWeight {c : X → (D → ℝ) × (Fin r → ℝ)} (hc : Measurable c)
    (ra : D → ℝ) (rb : Fin r → ℝ) (τ : D → ℝ) : Measurable (siegelWeight c ra rb τ) := by
  have hreg : MeasurableSet (siegelRegion (r := r) τ) := by
    have h : siegelRegion (r := r) τ = ⋂ β, {x | τ β < x.1 β} := by ext x; simp [siegelRegion]
    rw [h]
    exact MeasurableSet.iInter fun β =>
      measurableSet_lt measurable_const ((measurable_pi_apply β).comp measurable_fst)
  exact ((ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_const.mul
    (continuous_localFinitenessLogWeight ra rb).measurable))).indicator hreg).comp hc

theorem measurable_orthantWeight {c : X → (D → ℝ) × (Fin r → ℝ)} (hc : Measurable c)
    (ra : D → ℝ) (rb : Fin r → ℝ) (τ : D → ℝ) (J : D → Prop) (ε : Fin r → Bool) :
    Measurable (orthantWeight c ra rb τ J ε) :=
  ((ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_const.mul
    (continuous_orthantLogWeight ra rb ε).measurable))).indicator
      (measurableSet_leviRegion τ J)).comp hc

theorem measurableSet_orthantPos {c : X → (D → ℝ) × (Fin r → ℝ)} (hc : Measurable c)
    (τ : D → ℝ) (J : D → Prop) (ε : Fin r → Bool) : MeasurableSet (orthantPos c τ J ε) := by
  have h : orthantPos c τ J ε = ⋂ k, {g | 0 < orthantHeight c τ J ε k g} := by
    ext g; simp [orthantPos]
  rw [h]
  refine MeasurableSet.iInter fun k => measurableSet_lt measurable_const ?_
  rcases k with β | j
  · exact (((measurable_pi_apply β.1).comp measurable_fst).comp hc).sub_const _
  · refine Measurable.add_const ?_ _
    unfold orthantCoord
    by_cases hε : ε j
    · simp only [hε, ↓reduceIte]
      exact ((measurable_pi_apply j).comp measurable_snd).comp hc
    · simp only [hε, Bool.false_eq_true, ↓reduceIte]
      exact (((measurable_pi_apply j).comp measurable_snd).comp hc).neg

/-- The Siegel-weighted measure is dominated by the sum of the orthant-weighted measures on the
positive regions. -/
theorem withDensity_siegelWeight_le (ν : Measure X) {c : X → (D → ℝ) × (Fin r → ℝ)}
    (hc : Measurable c) (ra : D → ℝ) (rb : Fin r → ℝ) (τ : D → ℝ) (J : D → Prop) :
    ν.withDensity (siegelWeight c ra rb τ) ≤
      ∑ ε : Fin r → Bool, (ν.withDensity (orthantWeight c ra rb τ J ε)).restrict
        (orthantPos c τ J ε) := by
  refine Measure.le_iff.mpr fun t ht => ?_
  rw [withDensity_apply _ ht, Measure.coe_finsetSum, Finset.sum_apply]
  have hterm (ε : Fin r → Bool) :
      ((ν.withDensity (orthantWeight c ra rb τ J ε)).restrict (orthantPos c τ J ε)) t =
        ∫⁻ g in t, (orthantPos c τ J ε).indicator (orthantWeight c ra rb τ J ε) g ∂ν := by
    rw [Measure.restrict_apply ht, withDensity_apply _ (ht.inter (measurableSet_orthantPos hc τ J ε)),
      lintegral_indicator (measurableSet_orthantPos hc τ J ε), Measure.restrict_restrict
        (measurableSet_orthantPos hc τ J ε), Set.inter_comm]
  simp_rw [hterm]
  rw [← lintegral_finsetSum _ fun ε _ =>
    (measurable_orthantWeight hc ra rb τ J ε).indicator (measurableSet_orthantPos hc τ J ε)]
  exact setLIntegral_mono (Finset.measurable_sum _ fun ε _ =>
    (measurable_orthantWeight hc ra rb τ J ε).indicator (measurableSet_orthantPos hc τ J ε))
    fun g _ => siegelWeight_le_sum c ra rb τ J g

/-- On a subset of the positive region, the orthant-weighted measure is at most
`exp(4 ∑_j rb_j)` times the Siegel-weighted measure. -/
theorem restrict_withDensity_orthantWeight_le (ν : Measure X) {c : X → (D → ℝ) × (Fin r → ℝ)}
    (hc : Measurable c) (ra : D → ℝ) (rb : Fin r → ℝ) (hrb : ∀ j, 0 ≤ rb j) (τ : D → ℝ)
    (J : D → Prop) (ε : Fin r → Bool) {S : Set X} (hS : MeasurableSet S)
    (hSp : S ⊆ orthantPos c τ J ε) :
    (ν.withDensity (orthantWeight c ra rb τ J ε)).restrict S ≤
      ENNReal.ofReal (Real.exp (4 * ∑ j, rb j)) •
        (ν.withDensity (siegelWeight c ra rb τ)).restrict S := by
  refine Measure.le_iff.mpr fun t ht => ?_
  rw [Measure.smul_apply, Measure.restrict_apply ht, Measure.restrict_apply ht,
    withDensity_apply _ (ht.inter hS), withDensity_apply _ (ht.inter hS), smul_eq_mul,
    ← lintegral_const_mul _ (measurable_siegelWeight hc ra rb τ)]
  refine setLIntegral_mono ((measurable_siegelWeight hc ra rb τ).const_mul _) fun g hg => ?_
  have h := orthantWeight_le_siegelWeight c ra rb hrb τ J ε g
  rwa [indicator_of_mem (hSp hg.2)] at h

end Measures

section Combination

variable [MeasurableSpace X]

/-- The `L²` norm for the orthant weight on a subset of its positive region is at most
`exp(2 ∑_j rb_j)` times the norm for the Siegel weight. -/
theorem lpNorm_orthant_le (ν : Measure X) {c : X → (D → ℝ) × (Fin r → ℝ)} (hc : Measurable c)
    (ra : D → ℝ) (rb : Fin r → ℝ) (hrb : ∀ j, 0 ≤ rb j) (τ : D → ℝ) (J : D → Prop)
    (ε : Fin r → Bool) {S : Set X} (hS : MeasurableSet S) (hSp : S ⊆ orthantPos c τ J ε)
    {f : X → ℂ} (hf : MemLp f 2 ((ν.withDensity (siegelWeight c ra rb τ)).restrict S)) :
    lpNorm f 2 ((ν.withDensity (orthantWeight c ra rb τ J ε)).restrict S) ≤
      Real.exp (2 * ∑ j, rb j) * lpNorm f 2 ((ν.withDensity (siegelWeight c ra rb τ)).restrict S) := by
  have h := eLpNorm_le_of_measure_le_smul
    (restrict_withDensity_orthantWeight_le ν hc ra rb hrb τ J ε hS hSp) (f := f) (p := 2)
  have hK : ENNReal.ofReal (Real.exp (4 * ∑ j, rb j)) ^ (1 / (2 : ℝ≥0∞)).toReal =
      ENNReal.ofReal (Real.exp (2 * ∑ j, rb j)) := by
    rw [ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le (by norm_num), ← Real.exp_mul]
    congr 2
    norm_num
    ring
  rw [hK] at h
  unfold lpNorm
  calc (eLpNorm f 2 ((ν.withDensity (orthantWeight c ra rb τ J ε)).restrict S)).toReal
      ≤ (ENNReal.ofReal (Real.exp (2 * ∑ j, rb j)) •
          eLpNorm f 2 ((ν.withDensity (siegelWeight c ra rb τ)).restrict S)).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hf.eLpNorm_ne_top) h
    _ = _ := by
        rw [smul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le]

/-- **From orthant estimates to the Siegel weight.** If, on every central orthant, the slab
estimate holds for the orthant weight with constant `C ε`, then a function whose boxes and
residuals are square integrable for the Siegel weight is square integrable for the Siegel
weight, with norm at most `exp(2 ∑_j rb_j) ∑_ε C ε (‖φ‖_box + ∑_k ‖res‖_pos)`. -/
theorem siegel_estimate_of_orthants (ν : Measure X) {c : X → (D → ℝ) × (Fin r → ℝ)}
    (hc : Measurable c) (ra : D → ℝ) (rb : Fin r → ℝ) (hrb : ∀ j, 0 ≤ rb j) (τ : D → ℝ)
    (J : D → Prop) {I : (Fin r → Bool) → Type*} [∀ ε, Fintype (I ε)]
    (box : (Fin r → Bool) → Set X) (hbox : ∀ ε, MeasurableSet (box ε))
    (hboxpos : ∀ ε, box ε ⊆ orthantPos c τ J ε) (C : (Fin r → Bool) → ℝ) (hC : ∀ ε, 0 ≤ C ε)
    {φ : X → ℂ} (hφ : Measurable φ) (res : ∀ ε, I ε → X → ℂ)
    (H : ∀ ε, MemLp φ 2 ((ν.withDensity (orthantWeight c ra rb τ J ε)).restrict (box ε)) →
      (∀ k, MemLp (res ε k) 2
        ((ν.withDensity (orthantWeight c ra rb τ J ε)).restrict (orthantPos c τ J ε))) →
      MemLp φ 2 ((ν.withDensity (orthantWeight c ra rb τ J ε)).restrict (orthantPos c τ J ε)) ∧
      lpNorm φ 2 ((ν.withDensity (orthantWeight c ra rb τ J ε)).restrict (orthantPos c τ J ε)) ≤
        C ε * (lpNorm φ 2 ((ν.withDensity (orthantWeight c ra rb τ J ε)).restrict (box ε)) +
          ∑ k, lpNorm (res ε k) 2
            ((ν.withDensity (orthantWeight c ra rb τ J ε)).restrict (orthantPos c τ J ε))))
    (hboxB : ∀ ε, MemLp φ 2 ((ν.withDensity (siegelWeight c ra rb τ)).restrict (box ε)))
    (hresB : ∀ ε k, MemLp (res ε k) 2
      ((ν.withDensity (siegelWeight c ra rb τ)).restrict (orthantPos c τ J ε))) :
    MemLp φ 2 (ν.withDensity (siegelWeight c ra rb τ)) ∧
      lpNorm φ 2 (ν.withDensity (siegelWeight c ra rb τ)) ≤
        Real.exp (2 * ∑ j, rb j) * ∑ ε, C ε *
          (lpNorm φ 2 ((ν.withDensity (siegelWeight c ra rb τ)).restrict (box ε)) +
            ∑ k, lpNorm (res ε k) 2
              ((ν.withDensity (siegelWeight c ra rb τ)).restrict (orthantPos c τ J ε))) := by
  set μB := ν.withDensity (siegelWeight c ra rb τ)
  set μ := fun ε => ν.withDensity (orthantWeight c ra rb τ J ε)
  set pos := fun ε => orthantPos c τ J ε
  set k := Real.exp (2 * ∑ j, rb j)
  have hKt : ENNReal.ofReal (Real.exp (4 * ∑ j, rb j)) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hpm (ε) : MeasurableSet (pos ε) := measurableSet_orthantPos hc τ J ε
  have hboxε (ε) : MemLp φ 2 ((μ ε).restrict (box ε)) :=
    (hboxB ε).of_measure_le_smul hKt
      (restrict_withDensity_orthantWeight_le ν hc ra rb hrb τ J ε (hbox ε) (hboxpos ε))
  have hresε (ε) (q) : MemLp (res ε q) 2 ((μ ε).restrict (pos ε)) :=
    (hresB ε q).of_measure_le_smul hKt
      (restrict_withDensity_orthantWeight_le ν hc ra rb hrb τ J ε (hpm ε) subset_rfl)
  choose hmem hbound using fun ε => H ε (hboxε ε) (hresε ε)
  have hle := withDensity_siegelWeight_le ν hc ra rb τ J
  have hsum : MemLp φ 2 (∑ ε, (μ ε).restrict (pos ε)) :=
    memLp_two_finset_sum_measure _ _ fun ε _ => hmem ε
  refine ⟨hsum.mono_measure hle, ?_⟩
  have h1 : lpNorm φ 2 μB ≤ ∑ ε, lpNorm φ 2 ((μ ε).restrict (pos ε)) := by
    unfold lpNorm
    rw [← ENNReal.toReal_sum fun ε _ => (hmem ε).eLpNorm_ne_top]
    refine ENNReal.toReal_mono (ENNReal.sum_ne_top.mpr fun ε _ => (hmem ε).eLpNorm_ne_top) ?_
    exact (eLpNorm_mono_measure φ hle).trans (eLpNorm_two_finset_sum_measure_le hφ _ _)
  refine h1.trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun ε _ => (hbound ε).trans ?_
  have hb := lpNorm_orthant_le ν hc ra rb hrb τ J ε (hbox ε) (hboxpos ε) (hboxB ε)
  have hr (q : I ε) := lpNorm_orthant_le ν hc ra rb hrb τ J ε (hpm ε) subset_rfl (hresB ε q)
  have hrs : ∑ q, lpNorm (res ε q) 2 ((μ ε).restrict (pos ε)) ≤
      k * ∑ q, lpNorm (res ε q) 2 (μB.restrict (pos ε)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun q _ => hr q
  calc C ε * (lpNorm φ 2 ((μ ε).restrict (box ε)) +
        ∑ q, lpNorm (res ε q) 2 ((μ ε).restrict (pos ε)))
      ≤ C ε * (k * lpNorm φ 2 (μB.restrict (box ε)) +
        k * ∑ q, lpNorm (res ε q) 2 (μB.restrict (pos ε))) :=
        mul_le_mul_of_nonneg_left (add_le_add hb hrs) (hC ε)
    _ = k * (C ε * (lpNorm φ 2 (μB.restrict (box ε)) +
        ∑ q, lpNorm (res ε q) 2 (μB.restrict (pos ε)))) := by ring

end Combination

end Langlands.Global.StandardConstantTerm
