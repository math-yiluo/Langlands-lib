import Mathlib.MeasureTheory.Group.ModularCharacter
import Mathlib.MeasureTheory.Group.Convolution

/-! # Bounding the modular character by a locally comparable measure -/

noncomputable section

open MeasureTheory Measure Filter Topology Set
open scoped NNReal ENNReal Pointwise

namespace Langlands.Global.LocalModularCharacter

variable {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [LocallyCompactSpace H] [T2Space H] [SecondCountableTopology H]
  [MeasurableSpace H] [BorelSpace H]

omit [T2Space H] in
/-- Conjugation by `g` scales every left Haar measure by the modular character. -/
theorem measure_conj_image (μ : Measure H) [IsHaarMeasure μ] (g : H) (V : Set H) :
    μ ((fun x => g * x * g⁻¹) '' V) = (modularCharacter g : ℝ≥0∞) * μ V := by
  have hmap : map (· * g) μ = modularCharacter g • μ := by
    change map (· * g) μ = modularCharacterFun g • μ
    rw [modularCharacterFun_eq_haarScalarFactor μ g]
    exact isMulLeftInvariant_eq_smul _ μ
  have himage : (fun x => g * x * g⁻¹) '' V =
      (fun y => g⁻¹ * y) ⁻¹' ((fun y => y * g) ⁻¹' V) := by
    ext y
    simp only [mem_image, mem_preimage]
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa [mul_assoc] using hx
    · intro hy
      exact ⟨g⁻¹ * y * g, hy, by simp [mul_assoc]⟩
  have hpre : μ ((fun y => y * g) ⁻¹' V) = map (· * g) μ V :=
    ((MeasurableEquiv.mulRight g).map_apply V).symm
  rw [himage, measure_preimage_mul, hpre, hmap, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]

variable (μ ν : Measure H) [IsHaarMeasure μ]

omit [LocallyCompactSpace H] [T2Space H] [IsHaarMeasure μ] in
/-- The convolution of Haar measure with a restricted comparison measure. -/
theorem mconv_restrict_apply [SFinite ν] {W S : Set H} (hS : MeasurableSet S) :
    (μ ∗ₘ ν.restrict W) S = ∫⁻ x, ν (W ∩ (fun y => x * y) ⁻¹' S) ∂μ := by
  rw [mconv, map_apply measurable_mul hS, prod_apply (measurable_mul hS)]
  refine lintegral_congr fun x => ?_
  change (ν.restrict W) ((fun y => x * y) ⁻¹' S) = _
  rw [restrict_apply (measurable_const_mul x hS), inter_comm]

omit [LocallyCompactSpace H] [T2Space H] in
/-- The convolution of a left-invariant measure with any measure is left-invariant. -/
theorem isMulLeftInvariant_mconv_restrict [SFinite ν] (W : Set H) :
    IsMulLeftInvariant (μ ∗ₘ ν.restrict W) := by
  constructor
  intro g
  ext S hS
  rw [map_apply (measurable_const_mul g) hS, mconv_restrict_apply μ ν hS,
    mconv_restrict_apply μ ν ((measurable_const_mul g) hS)]
  have : ∀ x : H, (fun y => x * y) ⁻¹' ((fun h => g * h) ⁻¹' S) =
      (fun y => (g * x) * y) ⁻¹' S := by
    intro x
    ext y
    simp [mul_assoc]
  simp_rw [this]
  exact lintegral_mul_left_eq_self (fun x => ν (W ∩ (fun y => x * y) ⁻¹' S)) g

omit [LocallyCompactSpace H] in
/-- If the restricting set lies in a compact set, the convolution is finite on compacts. -/
theorem isFiniteMeasureOnCompacts_mconv_restrict [IsFiniteMeasure ν] {W K : Set H}
    (hK : IsCompact K) (hWK : W ⊆ K) :
    IsFiniteMeasureOnCompacts (μ ∗ₘ ν.restrict W) := by
  constructor
  intro C hC
  have hCK : IsCompact (C * K⁻¹) := hC.mul hK.inv
  rw [mconv_restrict_apply μ ν hC.isClosed.measurableSet]
  calc ∫⁻ x, ν (W ∩ (fun y => x * y) ⁻¹' C) ∂μ
      ≤ ∫⁻ x, (C * K⁻¹).indicator (fun _ => ν univ) x ∂μ := by
        refine lintegral_mono fun x => ?_
        by_cases hx : x ∈ C * K⁻¹
        · rw [indicator_of_mem hx]
          exact measure_mono (subset_univ _)
        · rw [indicator_of_notMem hx]
          have : W ∩ (fun y => x * y) ⁻¹' C = ∅ := by
            ext y
            simp only [mem_inter_iff, mem_preimage, mem_empty_iff_false, iff_false, not_and]
            intro hy hxy
            exact hx ⟨x * y, hxy, y⁻¹, by simpa using hWK hy, by simp⟩
          rw [this, measure_empty]
    _ = ν univ * μ (C * K⁻¹) := lintegral_indicator_const hCK.isClosed.measurableSet _
    _ < ∞ := ENNReal.mul_lt_top (measure_lt_top ν univ) hCK.measure_lt_top

omit [T2Space H] in
/-- The swapped integral of the comparison measure of translates. -/
theorem lintegral_measure_translate_inter [SFinite ν] {W S : Set H}
    (hW : MeasurableSet W) (hS : MeasurableSet S) :
    ∫⁻ x, ν ((fun y => x * y) '' W ∩ S) ∂μ = μ W⁻¹ * ν S := by
  let P : Set (H × H) := {p | p.1⁻¹ * p.2 ∈ W ∧ p.2 ∈ S}
  have hP : MeasurableSet P :=
    (hW.preimage (measurable_fst.inv.mul measurable_snd)).inter (hS.preimage measurable_snd)
  have hx : ∀ x : H, (fun y => x * y) '' W ∩ S = Prod.mk x ⁻¹' P := by
    intro x
    rw [image_mul_left]
    rfl
  simp_rw [hx]
  rw [← prod_apply hP, prod_apply_symm hP]
  have hy : ∀ y : H, μ ((fun x => (x, y)) ⁻¹' P) = S.indicator (fun _ => μ W⁻¹) y := by
    intro y
    by_cases hyS : y ∈ S
    · rw [indicator_of_mem hyS]
      have : (fun x => (x, y)) ⁻¹' P = (fun x => y⁻¹ * x) ⁻¹' W⁻¹ := by
        ext x
        simp only [mem_preimage]
        change (x⁻¹ * y ∈ W ∧ y ∈ S) ↔ y⁻¹ * x ∈ W⁻¹
        rw [show y⁻¹ * x = (x⁻¹ * y)⁻¹ by rw [mul_inv_rev, inv_inv], Set.mem_inv, inv_inv]
        simp [hyS]
      rw [this, measure_preimage_mul]
    · rw [indicator_of_notMem hyS]
      have : (fun x => (x, y)) ⁻¹' P = ∅ := by
        ext x
        simp [P, hyS]
      rw [this, measure_empty]
  simp_rw [hy]
  rw [lintegral_indicator_const hS]

omit [LocallyCompactSpace H] [T2Space H] [SecondCountableTopology H] in
/-- Pointwise comparison of the two integrands: when the translate meets `S`, both translations
involved stay in `N`, where translation changes `ν` by at most the factor `η`. -/
theorem measure_inter_translate_le {ν : Measure H} {N O W S : Set H} {η : ℝ≥0∞}
    (happ : ∀ x ∈ N, ∀ T ⊆ N, MeasurableSet T → ν ((x * ·) '' T) ≤ η * ν T)
    (hON : O * O⁻¹ ⊆ N) (h1O : (1 : H) ∈ O) (hWO : W ⊆ O) (hSO : S ⊆ O)
    (hW : MeasurableSet W) (hS : MeasurableSet S) (x : H) :
    ν (W ∩ (fun y => x * y) ⁻¹' S) ≤ η * ν ((fun y => x * y) '' W ∩ S) ∧
      ν ((fun y => x * y) '' W ∩ S) ≤ η * ν (W ∩ (fun y => x * y) ⁻¹' S) := by
  have hT : (fun y => x * y) '' W ∩ S = (fun y => x * y) '' (W ∩ (fun y => x * y) ⁻¹' S) :=
    (image_inter_preimage _ _ _).symm
  have hTm : MeasurableSet ((fun y => x * y) '' W ∩ S) := by
    rw [image_mul_left]
    exact (measurable_const_mul x⁻¹ hW).inter hS
  rw [hT] at hTm
  rw [hT]
  set R := W ∩ (fun y => x * y) ⁻¹' S with hR
  rcases R.eq_empty_or_nonempty with hR0 | ⟨y, hyW, hyS⟩
  · simp [hR0]
  have hyS' : x * y ∈ S := hyS
  have hON' : O ⊆ N := fun z hz => hON ⟨z, hz, 1, by simpa using h1O, mul_one z⟩
  have hxN : x ∈ N :=
    hON ⟨x * y, hSO hyS', y⁻¹, by simpa using hWO hyW, mul_inv_cancel_right x y⟩
  have hxN' : x⁻¹ ∈ N :=
    hON ⟨y, hWO hyW, (x * y)⁻¹, by simpa using hSO hyS', by simp⟩
  have hRN : R ⊆ N := fun z hz => hON' (hWO hz.1)
  have hRm : MeasurableSet R := hW.inter (measurable_const_mul x hS)
  have hTN : (fun y => x * y) '' R ⊆ N := by
    rintro _ ⟨z, hz, rfl⟩
    exact hON' (hSO hz.2)
  have hback : (fun z => x⁻¹ * z) '' ((fun y => x * y) '' R) = R := by
    rw [image_image]
    simp
  refine ⟨?_, happ x hxN R hRN hRm⟩
  calc ν R = ν ((fun z => x⁻¹ * z) '' ((fun y => x * y) '' R)) := by rw [hback]
    _ ≤ η * ν ((fun y => x * y) '' R) := happ x⁻¹ hxN' _ hTN hTm

/-- The modular character is bounded by `(1 + η) ^ 3 * D` as soon as a finite comparison measure
`ν`, positive on neighbourhoods of `1`, is translation invariant up to the factor `1 + η` near
`1`, and conjugation by `g` scales arbitrarily small open neighbourhoods of `1` by at most
`(1 + η) * D`. -/
theorem modularCharacter_le_of_comparison_aux (μ ν : Measure H) [IsHaarMeasure μ]
    [IsFiniteMeasure ν] (g : H) (D η : ℝ≥0) (hpos : ∀ U ∈ 𝓝 (1 : H), 0 < ν U)
    {N : Set H} (hN : N ∈ 𝓝 (1 : H))
    (happ : ∀ x ∈ N, ∀ T ⊆ N, MeasurableSet T → ν ((x * ·) '' T) ≤ (1 + η) * ν T)
    (hdet : ∀ U ∈ 𝓝 (1 : H), ∃ V ⊆ U, IsOpen V ∧ (1 : H) ∈ V ∧
      ν ((fun x => g * x * g⁻¹) '' V) ≤ (1 + η) * D * ν V) :
    modularCharacter g ≤ (1 + η) ^ 3 * D := by
  obtain ⟨O₀, hO₀, h1O₀, hO₀N⟩ := exists_open_nhds_one_mul_subset hN
  set O := O₀ ∩ O₀⁻¹ with hOdef
  have hO : IsOpen O := hO₀.inter hO₀.inv
  have h1O : (1 : H) ∈ O := ⟨h1O₀, by simpa using h1O₀⟩
  have hON : O * O⁻¹ ⊆ N := by
    refine Subset.trans (mul_subset_mul inter_subset_left ?_) hO₀N
    rw [hOdef, inter_inv, inv_inv]
    exact inter_subset_right
  obtain ⟨K, hK, hKn⟩ := exists_compact_mem_nhds (1 : H)
  set W := O ∩ interior K with hWdef
  have hWo : IsOpen W := hO.inter isOpen_interior
  have hWn : W ∈ 𝓝 (1 : H) := inter_mem (hO.mem_nhds h1O) (interior_mem_nhds.2 hKn)
  have hWO : W ⊆ O := inter_subset_left
  have hWK : W ⊆ K := inter_subset_right.trans interior_subset
  have hWm : MeasurableSet W := hWo.measurableSet
  have := isMulLeftInvariant_mconv_restrict μ ν W
  have := isFiniteMeasureOnCompacts_mconv_restrict μ ν hK hWK
  have hF := isMulLeftInvariant_eq_smul (μ ∗ₘ ν.restrict W) μ
  set c := haarScalarFactor (μ ∗ₘ ν.restrict W) μ
  set a := μ W⁻¹ with ha
  have ha0 : a ≠ 0 := (measure_pos_of_mem_nhds μ (inv_mem_nhds_one H hWn)).ne'
  have haT : a ≠ ∞ :=
    (lt_of_le_of_lt (measure_mono (inv_subset_inv.2 hWK)) hK.inv.measure_lt_top).ne
  have hFS : ∀ S, (μ ∗ₘ ν.restrict W) S = c * μ S := by
    intro S
    rw [hF, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
  have hI : ∀ S, MeasurableSet S → S ⊆ O →
      (c : ℝ≥0∞) * μ S ≤ (1 + η) * (a * ν S) ∧ a * ν S ≤ (1 + η) * ((c : ℝ≥0∞) * μ S) := by
    intro S hS hSO
    have hpt := fun x => measure_inter_translate_le happ hON h1O hWO hSO hWm hS x
    refine ⟨?_, ?_⟩
    · calc (c : ℝ≥0∞) * μ S = ∫⁻ x, ν (W ∩ (fun y => x * y) ⁻¹' S) ∂μ := by
            rw [← hFS S, mconv_restrict_apply μ ν hS]
        _ ≤ ∫⁻ x, (1 + η) * ν ((fun y => x * y) '' W ∩ S) ∂μ :=
            lintegral_mono fun x => (hpt x).1
        _ = (1 + η) * (a * ν S) := by
            rw [lintegral_const_mul' _ _ (by simp), lintegral_measure_translate_inter μ ν hWm hS]
    · calc a * ν S = ∫⁻ x, ν ((fun y => x * y) '' W ∩ S) ∂μ :=
            (lintegral_measure_translate_inter μ ν hWm hS).symm
        _ ≤ ∫⁻ x, (1 + η) * ν (W ∩ (fun y => x * y) ⁻¹' S) ∂μ :=
            lintegral_mono fun x => (hpt x).2
        _ = (1 + η) * ((c : ℝ≥0∞) * μ S) := by
            rw [lintegral_const_mul' _ _ (by simp), ← mconv_restrict_apply μ ν hS, hFS S]
  have hc0 : (c : ℝ≥0∞) ≠ 0 := by
    intro h
    have := (hI W hWm hWO).2
    rw [h, zero_mul, mul_zero] at this
    exact (ENNReal.mul_pos ha0 (hpos W hWn).ne').ne' (nonpos_iff_eq_zero.1 this)
  have hconj_cont : Continuous (fun x : H => g * x * g⁻¹) := by fun_prop
  have hUn : W ∩ (fun x => g * x * g⁻¹) ⁻¹' O ∈ 𝓝 (1 : H) := by
    refine inter_mem hWn (hconj_cont.continuousAt.preimage_mem_nhds ?_)
    simpa using hO.mem_nhds h1O
  obtain ⟨V, hVU, hVo, h1V, hVdet⟩ := hdet _ hUn
  have hVO : V ⊆ O := fun x hx => hWO (hVU hx).1
  have hVK : V ⊆ K := fun x hx => hWK (hVU hx).1
  have hCO : (fun x => g * x * g⁻¹) '' V ⊆ O := by
    rintro _ ⟨x, hx, rfl⟩
    exact (hVU hx).2
  have hCm : MeasurableSet ((fun x => g * x * g⁻¹) '' V) := by
    have : (fun x => g * x * g⁻¹) '' V = (fun y => y * g⁻¹) '' ((fun x => g * x) '' V) := by
      rw [image_image]
    rw [this]
    exact ((isOpenMap_mul_right g⁻¹) _ ((isOpenMap_mul_left g) _ hVo)).measurableSet
  have hμV0 : μ V ≠ 0 := (hVo.measure_pos μ ⟨1, h1V⟩).ne'
  have hμVT : μ V ≠ ∞ := (lt_of_le_of_lt (measure_mono hVK) hK.measure_lt_top).ne
  have hI1 := (hI _ hCm hCO).1
  have hI2 := (hI V hVo.measurableSet hVO).2
  have key : (c : ℝ≥0∞) * μ V * (modularCharacter g : ℝ≥0∞) ≤
      (c : ℝ≥0∞) * μ V * (((1 + η) ^ 3 * D : ℝ≥0) : ℝ≥0∞) := by
    calc (c : ℝ≥0∞) * μ V * (modularCharacter g : ℝ≥0∞)
        = c * μ ((fun x => g * x * g⁻¹) '' V) := by rw [measure_conj_image μ g V]; ring
      _ ≤ (1 + η) * (a * ν ((fun x => g * x * g⁻¹) '' V)) := hI1
      _ ≤ (1 + η) * (a * ((1 + η) * D * ν V)) := by gcongr
      _ = (1 + η) ^ 2 * D * (a * ν V) := by ring
      _ ≤ (1 + η) ^ 2 * D * ((1 + η) * ((c : ℝ≥0∞) * μ V)) := by gcongr
      _ = (c : ℝ≥0∞) * μ V * (((1 + η) ^ 3 * D : ℝ≥0) : ℝ≥0∞) := by push_cast; ring
  exact ENNReal.coe_le_coe.1 ((ENNReal.mul_le_mul_iff_right (mul_ne_zero hc0 hμV0)
    (ENNReal.mul_ne_top ENNReal.coe_ne_top hμVT)).1 key)

/-- **Upper bound for the modular character.** Let `ν` be a finite measure, positive on
neighbourhoods of `1`, such that for every `η > 0` left translation by elements near `1` changes
`ν` on small measurable sets by at most the factor `1 + η`, and conjugation by `g` changes `ν` on
arbitrarily small open neighbourhoods of `1` by at most the factor `(1 + η) * D`. Then the
modular character of `g` is at most `D`. -/
theorem modularCharacter_le_of_comparison (ν : Measure H) [IsFiniteMeasure ν] (g : H) (D : ℝ≥0)
    (hpos : ∀ U ∈ 𝓝 (1 : H), 0 < ν U)
    (happrox : ∀ η : ℝ≥0, 0 < η → ∃ N ∈ 𝓝 (1 : H), ∀ x ∈ N, ∀ T ⊆ N, MeasurableSet T →
      ν ((x * ·) '' T) ≤ (1 + η) * ν T)
    (hdet : ∀ η : ℝ≥0, 0 < η → ∀ U ∈ 𝓝 (1 : H), ∃ V ⊆ U, IsOpen V ∧ (1 : H) ∈ V ∧
      ν ((fun x => g * x * g⁻¹) '' V) ≤ (1 + η) * D * ν V) :
    modularCharacter g ≤ D := by
  have key : ∀ η : ℝ≥0, 0 < η → modularCharacter g ≤ (1 + η) ^ 3 * D := by
    intro η hη
    obtain ⟨N, hN, happ⟩ := happrox η hη
    exact modularCharacter_le_of_comparison_aux haar ν g D η hpos hN happ (hdet η hη)
  have hlim : Tendsto (fun η : ℝ≥0 => (1 + η) ^ 3 * D) (𝓝[>] 0) (𝓝 D) := by
    have : Continuous (fun η : ℝ≥0 => (1 + η) ^ 3 * D) := by fun_prop
    simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
  exact ge_of_tendsto hlim (eventually_nhdsWithin_of_forall fun η hη => key η hη)

end Langlands.Global.LocalModularCharacter
