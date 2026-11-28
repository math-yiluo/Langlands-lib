import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-! # Iterated integrals against an arbitrary measure

For a family of functions indexed by an arbitrary measure space `(Ω, m)`, the integral over `Ω`
of an average over a finite measure is at most the mass times the supremum of the integrals over
`Ω`, provided the family is detected by a countable set of evaluation points. No finiteness of
`m` is assumed. -/

noncomputable section

set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal

namespace Langlands.Analysis

variable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]

/-- **Average against a finite measure, integrated over an arbitrary measure.** Let `ν` be a
finite measure on `X`, `m` any measure on `Ω`, and `F` jointly measurable. If a countable set `D`
detects vanishing (`F o` vanishes identically as soon as it vanishes on `D`), then
`∫_Ω ∫_X F ≤ ν(X) · sup_x ∫_Ω F(·, x)`. The proof restricts `m` to the set of `o` with
`F o ≠ 0` somewhere on `D`, which is σ-finite when the supremum is finite, and applies Tonelli's
theorem there. -/
theorem lintegral_lintegral_le_mul_iSup (m : Measure Ω) (ν : Measure X) [IsFiniteMeasure ν]
    {F : Ω → X → ℝ≥0∞} (hF : Measurable (Function.uncurry F)) {D : Set X}
    (hD : D.Countable) (hzero : ∀ o, (∀ x ∈ D, F o x = 0) → ∀ x, F o x = 0) :
    ∫⁻ o, ∫⁻ x, F o x ∂ν ∂m ≤ ν univ * ⨆ x, ∫⁻ o, F o x ∂m := by
  set M := ⨆ x, ∫⁻ o, F o x ∂m with hMdef
  by_cases hν : ν univ = 0
  · have h0 : ν = 0 := Measure.measure_univ_eq_zero.mp hν
    simp [h0]
  by_cases hM : M = ⊤
  · rw [hM, ENNReal.mul_top hν]
    exact le_top
  have hFx : ∀ x, Measurable fun o => F o x := fun x =>
    hF.comp (measurable_id.prodMk measurable_const)
  set S : Set Ω := ⋃ x ∈ D, {o | F o x ≠ 0} with hSdef
  have hSmeas : MeasurableSet S :=
    MeasurableSet.biUnion hD fun x _ => (hFx x) (measurableSet_singleton 0).compl
  have hout : ∀ o ∉ S, ∫⁻ x, F o x ∂ν = 0 := by
    intro o ho
    have hD0 : ∀ x ∈ D, F o x = 0 := by
      intro x hx
      by_contra h
      exact ho (mem_biUnion hx h)
    simp [hzero o hD0]
  have hinner : Measurable fun o => ∫⁻ x, F o x ∂ν := hF.lintegral_prod_right'
  have hLHS : ∫⁻ o, ∫⁻ x, F o x ∂ν ∂m = ∫⁻ o, ∫⁻ x, F o x ∂ν ∂(m.restrict S) := by
    rw [← lintegral_indicator hSmeas]
    congr 1
    funext o
    by_cases ho : o ∈ S
    · simp [ho]
    · simp [ho, hout o ho]
  -- `m` restricted to `S` is σ-finite.
  have hfin : ∀ x, ∀ k : ℕ, m {o | ((k : ℝ≥0∞) + 1)⁻¹ ≤ F o x} < ⊤ := by
    intro x k
    have hk : ((k : ℝ≥0∞) + 1)⁻¹ ≠ 0 := by simp
    calc m {o | ((k : ℝ≥0∞) + 1)⁻¹ ≤ F o x}
        ≤ (∫⁻ o, F o x ∂m) / ((k : ℝ≥0∞) + 1)⁻¹ :=
          meas_ge_le_lintegral_div (hFx x).aemeasurable hk (by simp)
      _ ≤ M / ((k : ℝ≥0∞) + 1)⁻¹ := by
          gcongr
          exact le_iSup (fun x => ∫⁻ o, F o x ∂m) x
      _ < ⊤ := by
          rw [ENNReal.div_eq_inv_mul, inv_inv]
          exact ENNReal.mul_lt_top (by simp) (lt_top_iff_ne_top.mpr hM)
  have : SigmaFinite (m.restrict S) := by
    let C : Set (Set Ω) := insert Sᶜ
      ((fun p : X × ℕ => {o | ((p.2 : ℝ≥0∞) + 1)⁻¹ ≤ F o p.1}) '' (D ×ˢ univ))
    refine Measure.sigmaFinite_of_countable (S := C) ?_ ?_ ?_
    · exact ((hD.prod countable_univ).image _).insert _
    · intro s hs
      rcases hs with rfl | ⟨⟨x, k⟩, -, rfl⟩
      · rw [Measure.restrict_apply' hSmeas]
        simp
      · exact (Measure.restrict_apply_le _ _).trans_lt (hfin x k)
    · apply eq_univ_of_forall
      intro o
      by_cases ho : o ∈ S
      · obtain ⟨x, hx, hFo⟩ := mem_iUnion₂.mp ho
        have hpos : 0 < F o x := pos_iff_ne_zero.mpr hFo
        obtain ⟨k, hk⟩ := ENNReal.exists_inv_nat_lt hFo
        refine mem_sUnion.mpr ⟨_, mem_insert_of_mem _ ⟨(x, k), ⟨hx, trivial⟩, rfl⟩, ?_⟩
        change ((k : ℝ≥0∞) + 1)⁻¹ ≤ F o x
        refine le_trans ?_ hk.le
        gcongr
        exact le_self_add
      · exact mem_sUnion.mpr ⟨_, mem_insert _ _, ho⟩
  rw [hLHS, lintegral_lintegral_swap (hF.aemeasurable)]
  calc ∫⁻ x, ∫⁻ o, F o x ∂(m.restrict S) ∂ν
      ≤ ∫⁻ _x, M ∂ν := by
        refine lintegral_mono fun x => ?_
        exact (lintegral_mono' Measure.restrict_le_self le_rfl).trans
          (le_iSup (fun x => ∫⁻ o, F o x ∂m) x)
    _ = ν univ * M := by rw [lintegral_const, mul_comm]

/-- **Average against a finite measure concentrated on a set.** Variant of
`lintegral_lintegral_le_mul_iSup` for a finite measure `ν` concentrated on a set `T`: the supremum is
taken over `T` only. The countable detecting set `D` lies in `T`. -/
theorem lintegral_lintegral_le_mul_iSup_of_ae (m : Measure Ω) (ν : Measure X) [IsFiniteMeasure ν]
    {F : Ω → X → ℝ≥0∞} (hF : Measurable (Function.uncurry F)) {T D : Set X} (hDT : D ⊆ T)
    (hD : D.Countable) (hT : ∀ᵐ x ∂ν, x ∈ T)
    (hzero : ∀ o, (∀ x ∈ D, F o x = 0) → ∀ x ∈ T, F o x = 0) :
    ∫⁻ o, ∫⁻ x, F o x ∂ν ∂m ≤ ν univ * ⨆ x ∈ T, ∫⁻ o, F o x ∂m := by
  set M := ⨆ x ∈ T, ∫⁻ o, F o x ∂m with hMdef
  by_cases hν : ν univ = 0
  · have h0 : ν = 0 := Measure.measure_univ_eq_zero.mp hν
    simp [h0]
  by_cases hM : M = ⊤
  · rw [hM, ENNReal.mul_top hν]
    exact le_top
  have hFx : ∀ x, Measurable fun o => F o x := fun x =>
    hF.comp (measurable_id.prodMk measurable_const)
  set S : Set Ω := ⋃ x ∈ D, {o | F o x ≠ 0} with hSdef
  have hSmeas : MeasurableSet S :=
    MeasurableSet.biUnion hD fun x _ => (hFx x) (measurableSet_singleton 0).compl
  have hout : ∀ o ∉ S, ∫⁻ x, F o x ∂ν = 0 := by
    intro o ho
    have hD0 : ∀ x ∈ D, F o x = 0 := by
      intro x hx
      by_contra h
      exact ho (mem_biUnion hx h)
    have hFo : Measurable (F o) := hF.comp (measurable_const.prodMk measurable_id)
    rw [lintegral_eq_zero_iff' hFo.aemeasurable]
    filter_upwards [hT] with x hx
    exact hzero o hD0 x hx
  have hinner : Measurable fun o => ∫⁻ x, F o x ∂ν := hF.lintegral_prod_right'
  have hLHS : ∫⁻ o, ∫⁻ x, F o x ∂ν ∂m = ∫⁻ o, ∫⁻ x, F o x ∂ν ∂(m.restrict S) := by
    rw [← lintegral_indicator hSmeas]
    congr 1
    funext o
    by_cases ho : o ∈ S
    · simp [ho]
    · simp [ho, hout o ho]
  have hfin : ∀ x ∈ D, ∀ k : ℕ, m {o | ((k : ℝ≥0∞) + 1)⁻¹ ≤ F o x} < ⊤ := by
    intro x hx k
    have hk : ((k : ℝ≥0∞) + 1)⁻¹ ≠ 0 := by simp
    calc m {o | ((k : ℝ≥0∞) + 1)⁻¹ ≤ F o x}
        ≤ (∫⁻ o, F o x ∂m) / ((k : ℝ≥0∞) + 1)⁻¹ :=
          meas_ge_le_lintegral_div (hFx x).aemeasurable hk (by simp)
      _ ≤ M / ((k : ℝ≥0∞) + 1)⁻¹ := by
          gcongr
          exact le_iSup₂ (f := fun x (_ : x ∈ T) => ∫⁻ o, F o x ∂m) x (hDT hx)
      _ < ⊤ := by
          rw [ENNReal.div_eq_inv_mul, inv_inv]
          exact ENNReal.mul_lt_top (by simp) (lt_top_iff_ne_top.mpr hM)
  have : SigmaFinite (m.restrict S) := by
    let C : Set (Set Ω) := insert Sᶜ
      ((fun p : X × ℕ => {o | ((p.2 : ℝ≥0∞) + 1)⁻¹ ≤ F o p.1}) '' (D ×ˢ univ))
    refine Measure.sigmaFinite_of_countable (S := C) ?_ ?_ ?_
    · exact ((hD.prod countable_univ).image _).insert _
    · intro s hs
      rcases hs with rfl | ⟨⟨x, k⟩, ⟨hx, -⟩, rfl⟩
      · rw [Measure.restrict_apply' hSmeas]
        simp
      · exact (Measure.restrict_apply_le _ _).trans_lt (hfin x hx k)
    · apply eq_univ_of_forall
      intro o
      by_cases ho : o ∈ S
      · obtain ⟨x, hx, hFo⟩ := mem_iUnion₂.mp ho
        obtain ⟨k, hk⟩ := ENNReal.exists_inv_nat_lt hFo
        refine mem_sUnion.mpr ⟨_, mem_insert_of_mem _ ⟨(x, k), ⟨hx, trivial⟩, rfl⟩, ?_⟩
        change ((k : ℝ≥0∞) + 1)⁻¹ ≤ F o x
        refine le_trans ?_ hk.le
        gcongr
        exact le_self_add
      · exact mem_sUnion.mpr ⟨_, mem_insert _ _, ho⟩
  rw [hLHS, lintegral_lintegral_swap (hF.aemeasurable)]
  calc ∫⁻ x, ∫⁻ o, F o x ∂(m.restrict S) ∂ν
      ≤ ∫⁻ _x, M ∂ν := by
        refine lintegral_mono_ae ?_
        filter_upwards [hT] with x hx
        exact (lintegral_mono' Measure.restrict_le_self le_rfl).trans
          (le_iSup₂ (f := fun x (_ : x ∈ T) => ∫⁻ o, F o x ∂m) x hx)
    _ = ν univ * M := by rw [lintegral_const, mul_comm]

/-- **Family fundamental theorem of calculus on `[0, 1]`.** Let `f o` have derivative `f' o t`
at every `t`, with `f' o` continuous and `(o, t) ↦ f' o t` jointly measurable. Then the integral
over an arbitrary measure space of `‖f o 1 - f o 0‖` is at most the supremum over `t ∈ [0, 1]`
of the integrals of `‖f' o t‖`. -/
theorem lintegral_enorm_sub_le_iSup_deriv (m : Measure Ω) {f f' : Ω → ℝ → ℂ}
    (hderiv : ∀ o t, HasDerivAt (f o) (f' o t) t) (hcont : ∀ o, Continuous (f' o))
    (hmeas : Measurable (Function.uncurry f')) :
    ∫⁻ o, ‖f o 1 - f o 0‖ₑ ∂m ≤ ⨆ t ∈ Icc (0 : ℝ) 1, ∫⁻ o, ‖f' o t‖ₑ ∂m := by
  let ν : Measure ℝ := volume.restrict (Icc (0 : ℝ) 1)
  have : IsFiniteMeasure ν := by
    refine ⟨?_⟩
    simp [ν, Real.volume_Icc]
  let F : Ω → ℝ → ℝ≥0∞ := fun o t => ‖f' o (projIcc (0 : ℝ) 1 zero_le_one t)‖ₑ
  have hproj : Measurable fun t : ℝ => (projIcc (0 : ℝ) 1 zero_le_one t : ℝ) :=
    (continuous_subtype_val.comp continuous_projIcc).measurable
  have hF : Measurable (Function.uncurry F) :=
    (hmeas.comp (measurable_fst.prodMk (hproj.comp measurable_snd))).enorm
  have hcontF : ∀ o, Continuous (F o) := fun o =>
    ((hcont o).comp (continuous_subtype_val.comp continuous_projIcc)).enorm
  have hzero : ∀ o, (∀ x ∈ range ((↑) : ℚ → ℝ), F o x = 0) → ∀ x, F o x = 0 := by
    intro o h x
    have hdense : DenseRange ((↑) : ℚ → ℝ) := Rat.denseRange_cast
    have hclosed : IsClosed {x | F o x = 0} := isClosed_eq (hcontF o) continuous_const
    have hsub : range ((↑) : ℚ → ℝ) ⊆ {x | F o x = 0} := fun x hx => h x hx
    exact (hclosed.closure_subset_iff.mpr hsub) (hdense.closure_range.symm ▸ mem_univ x)
  have hpoint : ∀ o, ‖f o 1 - f o 0‖ₑ ≤ ∫⁻ t, F o t ∂ν := by
    intro o
    have hint : IntervalIntegrable (f' o) volume 0 1 :=
      (hcont o).intervalIntegrable 0 1
    have hFTC : ∫ t in (0 : ℝ)..1, f' o t = f o 1 - f o 0 :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hderiv o t) hint
    rw [← hFTC, intervalIntegral.integral_of_le zero_le_one]
    refine (enorm_integral_le_lintegral_enorm _).trans ?_
    change _ ≤ ∫⁻ t in Icc (0 : ℝ) 1, F o t
    rw [Measure.restrict_congr_set Ioc_ae_eq_Icc]
    refine (setLIntegral_congr_fun measurableSet_Icc fun t ht => ?_).le
    simp [F, projIcc_of_mem _ ht]
  calc ∫⁻ o, ‖f o 1 - f o 0‖ₑ ∂m ≤ ∫⁻ o, ∫⁻ t, F o t ∂ν ∂m := lintegral_mono hpoint
    _ ≤ ν univ * ⨆ t, ∫⁻ o, F o t ∂m :=
        lintegral_lintegral_le_mul_iSup m ν hF (countable_range _) hzero
    _ ≤ 1 * ⨆ t ∈ Icc (0 : ℝ) 1, ∫⁻ o, ‖f' o t‖ₑ ∂m := by
        refine mul_le_mul' (le_of_eq (by simp [ν, Real.volume_Icc])) ?_
        refine iSup_le fun t => ?_
        have hmem : (projIcc (0 : ℝ) 1 zero_le_one t : ℝ) ∈ Icc (0 : ℝ) 1 :=
          (projIcc (0 : ℝ) 1 zero_le_one t).property
        exact le_iSup₂_of_le (f := fun t (_ : t ∈ Icc (0 : ℝ) 1) => ∫⁻ o, ‖f' o t‖ₑ ∂m)
          _ hmem le_rfl
    _ = ⨆ t ∈ Icc (0 : ℝ) 1, ∫⁻ o, ‖f' o t‖ₑ ∂m := one_mul _

/-- **Family fundamental theorem of calculus on `[0, 1]`, integrated form.** If
`f o 1 - f o 0 = ∫₀¹ f' o` for every `o`, with `f' o` continuous and `(o, t) ↦ f' o t` jointly
measurable, then the integral over an arbitrary measure space of `‖f o 1 - f o 0‖` is at most the
supremum over `t ∈ [0, 1]` of the integrals of `‖f' o t‖`. -/
theorem lintegral_enorm_sub_le_iSup_of_integral (m : Measure Ω) {f f' : Ω → ℝ → ℂ}
    (hint : ∀ o, f o 1 - f o 0 = ∫ t in (0 : ℝ)..1, f' o t) (hcont : ∀ o, Continuous (f' o))
    (hmeas : Measurable (Function.uncurry f')) :
    ∫⁻ o, ‖f o 1 - f o 0‖ₑ ∂m ≤ ⨆ t ∈ Icc (0 : ℝ) 1, ∫⁻ o, ‖f' o t‖ₑ ∂m := by
  let ν : Measure ℝ := volume.restrict (Icc (0 : ℝ) 1)
  have : IsFiniteMeasure ν := by
    refine ⟨?_⟩
    simp [ν, Real.volume_Icc]
  let F : Ω → ℝ → ℝ≥0∞ := fun o t => ‖f' o (projIcc (0 : ℝ) 1 zero_le_one t)‖ₑ
  have hproj : Measurable fun t : ℝ => (projIcc (0 : ℝ) 1 zero_le_one t : ℝ) :=
    (continuous_subtype_val.comp continuous_projIcc).measurable
  have hF : Measurable (Function.uncurry F) :=
    (hmeas.comp (measurable_fst.prodMk (hproj.comp measurable_snd))).enorm
  have hcontF : ∀ o, Continuous (F o) := fun o =>
    ((hcont o).comp (continuous_subtype_val.comp continuous_projIcc)).enorm
  have hzero : ∀ o, (∀ x ∈ range ((↑) : ℚ → ℝ), F o x = 0) → ∀ x, F o x = 0 := by
    intro o h x
    have hdense : DenseRange ((↑) : ℚ → ℝ) := Rat.denseRange_cast
    have hclosed : IsClosed {x | F o x = 0} := isClosed_eq (hcontF o) continuous_const
    have hsub : range ((↑) : ℚ → ℝ) ⊆ {x | F o x = 0} := fun x hx => h x hx
    exact (hclosed.closure_subset_iff.mpr hsub) (hdense.closure_range.symm ▸ mem_univ x)
  have hpoint : ∀ o, ‖f o 1 - f o 0‖ₑ ≤ ∫⁻ t, F o t ∂ν := by
    intro o
    rw [hint o, intervalIntegral.integral_of_le zero_le_one]
    refine (enorm_integral_le_lintegral_enorm _).trans ?_
    change _ ≤ ∫⁻ t in Icc (0 : ℝ) 1, F o t
    rw [Measure.restrict_congr_set Ioc_ae_eq_Icc]
    refine (setLIntegral_congr_fun measurableSet_Icc fun t ht => ?_).le
    simp [F, projIcc_of_mem _ ht]
  calc ∫⁻ o, ‖f o 1 - f o 0‖ₑ ∂m ≤ ∫⁻ o, ∫⁻ t, F o t ∂ν ∂m := lintegral_mono hpoint
    _ ≤ ν univ * ⨆ t, ∫⁻ o, F o t ∂m :=
        lintegral_lintegral_le_mul_iSup m ν hF (countable_range _) hzero
    _ ≤ 1 * ⨆ t ∈ Icc (0 : ℝ) 1, ∫⁻ o, ‖f' o t‖ₑ ∂m := by
        refine mul_le_mul' (le_of_eq (by simp [ν, Real.volume_Icc])) ?_
        refine iSup_le fun t => ?_
        have hmem : (projIcc (0 : ℝ) 1 zero_le_one t : ℝ) ∈ Icc (0 : ℝ) 1 :=
          (projIcc (0 : ℝ) 1 zero_le_one t).property
        exact le_iSup₂_of_le (f := fun t (_ : t ∈ Icc (0 : ℝ) 1) => ∫⁻ o, ‖f' o t‖ₑ ∂m)
          _ hmem le_rfl
    _ = ⨆ t ∈ Icc (0 : ℝ) 1, ∫⁻ o, ‖f' o t‖ₑ ∂m := one_mul _

end Langlands.Analysis
