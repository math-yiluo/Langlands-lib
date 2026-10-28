import Langlands.Global.ArchimedeanKernelConjugationAverageStatement
import Langlands.Global.ArchimedeanSmoothDifferential
import Langlands.Analysis.CompactLinearParameterIntegralProof
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Prod

/-! # Proof of compact conjugation averaging of actual smooth kernels -/

noncomputable section
universe u
open MeasureTheory Set Topology
open scoped Classical Manifold ContDiff Matrix.Norms.Operator Pointwise
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.ArchimedeanGL

namespace KernelConjugationAverage

section Haar

variable {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [LocallyCompactSpace H] [T2Space H] [MeasurableSpace H] [BorelSpace H]

/-- Right translation by a member of a compact subgroup does not change a left Haar
measure on sets with compact closure. The proof evaluates the Haar scalar factor on
`V * L`, a compact right `L`-invariant set of positive measure. -/
theorem map_mul_right_apply_of_mem_compact (μ : Measure H) [μ.IsHaarMeasure]
    (L : Subgroup H) (hL : IsCompact (L : Set H)) {k : H} (hk : k ∈ L)
    {s : Set H} (hs : IsCompact (closure s)) :
    Measure.map (· * k) μ s = μ s := by
  obtain ⟨V, hVc, hV1⟩ := exists_compact_mem_nhds (1 : H)
  have hAc : IsCompact (V * (L : Set H)) := hVc.mul hL
  have hAk : (· * k) ⁻¹' (V * (L : Set H)) = V * (L : Set H) := by
    ext x
    simp only [mem_preimage, Set.mem_mul, SetLike.mem_coe]
    constructor
    · rintro ⟨v, hv, l, hl, h⟩
      refine ⟨v, hv, l * k⁻¹, L.mul_mem hl (L.inv_mem hk), ?_⟩
      rw [← mul_assoc, h, mul_inv_cancel_right]
    · rintro ⟨v, hv, l, hl, h⟩
      refine ⟨v, hv, l * k, L.mul_mem hl hk, ?_⟩
      rw [← mul_assoc, h]
  have hpos : μ (V * (L : Set H)) ≠ 0 := by
    have h1 : 0 < μ V := μ.measure_pos_of_mem_nhds hV1
    have hsub : V ⊆ V * (L : Set H) := fun v hv => Set.mem_mul.2 ⟨v, hv, 1, L.one_mem, mul_one v⟩
    exact (h1.trans_le (measure_mono hsub)).ne'
  have hfin : μ (V * (L : Set H)) ≠ ⊤ := hAc.measure_lt_top.ne
  have hmapA : Measure.map (· * k) μ (V * (L : Set H)) = μ (V * (L : Set H)) := by
    rw [Measure.map_apply (measurable_mul_const k) hAc.isClosed.measurableSet, hAk]
  have hscalar := Measure.measure_isMulInvariant_eq_smul_of_isCompact_closure
    (Measure.map (· * k) μ) μ (s := V * (L : Set H)) (by rw [hAc.isClosed.closure_eq]; exact hAc)
  rw [hmapA, ENNReal.smul_def, smul_eq_mul] at hscalar
  have hc : Measure.haarScalarFactor (Measure.map (· * k) μ) μ = 1 := by
    have h' : ((Measure.haarScalarFactor (Measure.map (· * k) μ) μ : NNReal) : ENNReal) = 1 :=
      (ENNReal.mul_eq_right hpos hfin).mp hscalar.symm
    exact_mod_cast h'
  rw [Measure.measure_isMulInvariant_eq_smul_of_isCompact_closure _ μ hs, hc, one_smul]

/-- Conjugation by a member of a compact subgroup preserves every left Haar integral of a
compactly supported complex function. -/
theorem integral_conj_of_mem_compact (μ : Measure H) [μ.IsHaarMeasure]
    (L : Subgroup H) (hL : IsCompact (L : Set H)) {k : H} (hk : k ∈ L)
    {φ : H → ℂ} (hφ : HasCompactSupport φ) :
    ∫ x, φ (k⁻¹ * x * k) ∂μ = ∫ x, φ x ∂μ := by
  have h1 : ∫ x, φ (k⁻¹ * x * k) ∂μ = ∫ x, φ (x * k) ∂μ :=
    integral_mul_left_eq_self (fun x => φ (x * k)) k⁻¹
  have h2 : ∫ x, φ (x * k) ∂μ = ∫ x, φ x ∂(Measure.map (· * k) μ) := by
    rw [← MeasurableEquiv.coe_mulRight k, integral_map_equiv]
    rfl
  have hrestr : (Measure.map (· * k) μ).restrict (tsupport φ) = μ.restrict (tsupport φ) := by
    ext T hT
    rw [Measure.restrict_apply hT, Measure.restrict_apply hT]
    apply map_mul_right_apply_of_mem_compact μ L hL hk
    exact hφ.isCompact.of_isClosed_subset isClosed_closure
      (closure_minimal inter_subset_right (isClosed_tsupport φ))
  have hzero : ∀ x, x ∉ tsupport φ → φ x = 0 := fun x hx => image_eq_zero_of_notMem_tsupport hx
  rw [h1, h2, ← setIntegral_eq_integral_of_forall_compl_eq_zero (μ := Measure.map (· * k) μ) hzero,
    ← setIntegral_eq_integral_of_forall_compl_eq_zero (μ := μ) hzero, hrestr]

end Haar

variable {K : Type u} [Field K] [NumberField K] {n : ℕ}

/-- Conjugation by the coordinate matrix of a compact element, as a real-linear map of
the matrix coordinates: `a ↦ c⁻¹ * a * c`. -/
def conjugationMap (k : standardInfiniteCompact K n) :
    ArchimedeanMatrix K n →L[ℝ] ArchimedeanMatrix K n :=
  ContinuousLinearMap.mulLeftRight ℝ (ArchimedeanMatrix K n)
    (((archimedeanGLCoordinates K n k.val)⁻¹ : ArchimedeanGL K n) : ArchimedeanMatrix K n)
    ((archimedeanGLCoordinates K n k.val : ArchimedeanGL K n) : ArchimedeanMatrix K n)

theorem conjugationMap_units (k : standardInfiniteCompact K n) (g : ArchimedeanGL K n) :
    conjugationMap k (g : ArchimedeanMatrix K n) =
      (((archimedeanGLCoordinates K n k.val)⁻¹ * g * archimedeanGLCoordinates K n k.val :
        ArchimedeanGL K n) : ArchimedeanMatrix K n) := by
  simp only [conjugationMap, ContinuousLinearMap.mulLeftRight_apply, Units.val_mul]

theorem continuous_conjugationMap : Continuous (conjugationMap (K := K) (n := n)) := by
  have hc : Continuous fun k : standardInfiniteCompact K n =>
      archimedeanGLCoordinates K n k.val :=
    (archimedeanGLCoordinates K n).continuous.comp continuous_subtype_val
  have ha : Continuous fun k : standardInfiniteCompact K n =>
      (((archimedeanGLCoordinates K n k.val)⁻¹ : ArchimedeanGL K n) : ArchimedeanMatrix K n) :=
    Units.continuous_val.comp (hc.inv)
  have hb : Continuous fun k : standardInfiniteCompact K n =>
      ((archimedeanGLCoordinates K n k.val : ArchimedeanGL K n) : ArchimedeanMatrix K n) :=
    Units.continuous_val.comp hc
  exact ((ContinuousLinearMap.mulLeftRight ℝ (ArchimedeanMatrix K n)).continuous.comp ha).clm_apply
    hb

variable [MeasurableSpace (standardInfiniteCompact K n)]

/-- The pointwise compact conjugation average of a kernel. -/
def average (ν : Measure (standardInfiniteCompact K n)) (κ : SmoothCompactKernel K n)
    (x : InfiniteAdelicGL K n) : ℂ :=
  ∫ k : standardInfiniteCompact K n, κ.val.val (k.val⁻¹ * x * k.val) ∂ν

/-- The compact conjugation saturation of the closed support of a kernel. -/
def saturation (κ : SmoothCompactKernel K n) : Set (InfiniteAdelicGL K n) :=
  {x | ∃ k : standardInfiniteCompact K n, ∃ y ∈ tsupport κ.val.val, x = k.val * y * k.val⁻¹}

omit [MeasurableSpace (standardInfiniteCompact K n)] in
theorem isCompact_saturation (κ : SmoothCompactKernel K n) : IsCompact (saturation κ) := by
  have h : saturation κ =
      (fun p : standardInfiniteCompact K n × InfiniteAdelicGL K n =>
        p.1.val * p.2 * p.1.val⁻¹) '' (univ ×ˢ tsupport κ.val.val) := by
    ext x
    constructor
    · rintro ⟨k, y, hy, rfl⟩
      exact ⟨(k, y), ⟨mem_univ _, hy⟩, rfl⟩
    · rintro ⟨⟨k, y⟩, ⟨-, hy⟩, rfl⟩
      exact ⟨k, y, hy, rfl⟩
  rw [h]
  exact (isCompact_univ.prod (smoothCompactKernel_hasCompactSupport K n κ).isCompact).image
    (by fun_prop)

theorem average_eq_zero_of_notMem (ν : Measure (standardInfiniteCompact K n))
    (κ : SmoothCompactKernel K n) {x : InfiniteAdelicGL K n} (hx : x ∉ saturation κ) :
    average ν κ x = 0 := by
  have h : ∀ k : standardInfiniteCompact K n, κ.val.val (k.val⁻¹ * x * k.val) = 0 := by
    intro k
    apply image_eq_zero_of_notMem_tsupport
    intro hy
    exact hx ⟨k, _, hy, by group⟩
  simp [average, h]

theorem tsupport_average_subset (ν : Measure (standardInfiniteCompact K n))
    (κ : SmoothCompactKernel K n) : tsupport (average ν κ) ⊆ saturation κ := by
  apply closure_minimal _ (isCompact_saturation κ).isClosed
  intro x hx
  by_contra h
  exact hx (average_eq_zero_of_notMem ν κ h)

theorem average_hasCompactSupport (ν : Measure (standardInfiniteCompact K n))
    (κ : SmoothCompactKernel K n) : HasCompactSupport (average ν κ) :=
  (isCompact_saturation κ).of_isClosed_subset (isClosed_tsupport _) (tsupport_average_subset ν κ)

variable [BorelSpace (standardInfiniteCompact K n)]

/-- Genuine smoothness of the average, by differentiation under the compact integral in
the matrix coordinates. -/
theorem average_mem_smoothFunctions (ν : Measure (standardInfiniteCompact K n))
    [IsFiniteMeasure ν] (κ : SmoothCompactKernel K n) :
    average ν κ ∈ smoothFunctions K n := by
  change ContMDiff 𝓘(ℝ, ArchimedeanMatrix K n) 𝓘(ℝ, ℂ) ∞ _
  have hopen := (Units.isOpenEmbedding_val (R := ArchimedeanMatrix K n)).isOpen_range
  have hint := Langlands.Analysis.compactLinearParameterIntegral.{u, u, u}
    (standardInfiniteCompact K n) (ArchimedeanMatrix K n) (ArchimedeanMatrix K n) ν
    univ isCompact_univ
    (range (Units.val : ArchimedeanGL K n → ArchimedeanMatrix K n)) hopen
    (range (Units.val : ArchimedeanGL K n → ArchimedeanMatrix K n)) hopen
    (fun _ => 1) continuous_const conjugationMap continuous_conjugationMap
    (coordinateExtension K n κ.val) (coordinateExtension_contDiffOn K n κ.val)
    (by
      rintro k - _ ⟨g, rfl⟩
      exact ⟨_, (conjugationMap_units k g).symm⟩)
  intro g
  have hat := hint.1.contDiffAt (hopen.mem_nhds ⟨g, rfl⟩)
  have hcomp := hat.comp_contMDiffAt (Units.contMDiff_val (𝕜 := ℝ) (n := ∞) g)
  convert hcomp using 1
  funext x
  simp only [Function.comp_apply, Measure.restrict_univ, one_mul, conjugationMap_units,
    coordinateExtension_apply, map_mul, map_inv, ContinuousMulEquiv.symm_apply_apply, average]

end KernelConjugationAverage

open KernelConjugationAverage in
/-- Probability Haar averaging over the actual standard compact subgroup produces a compact
smooth conjugation-invariant kernel and preserves its inverse-kernel integral against every
left Haar measure. -/
theorem compactKernelConjugationAverage (K : Type u) [Field K] [NumberField K] (n : ℕ) :
    CompactKernelConjugationAverageStatement K n := by
  intro _ _ μ _ _ _ ν _ _ κ
  refine ⟨⟨⟨average ν κ, average_mem_smoothFunctions ν κ⟩, average_hasCompactSupport ν κ⟩,
    fun x => rfl, tsupport_average_subset ν κ, ?_, ?_, ?_, ?_⟩
  · -- conjugation invariance, by left invariance of `ν`
    intro k₀ x
    show average ν κ _ = average ν κ x
    unfold average
    rw [← integral_mul_left_eq_self
      (fun k : standardInfiniteCompact K n => κ.val.val (k.val⁻¹ * x * k.val)) k₀]
    congr 1
    funext k
    simp only [Subgroup.coe_mul, mul_inv_rev]
    group
  · -- identity value
    show average ν κ 1 = κ.val.val 1
    simp [average]
  · -- real nonnegative values
    intro hκ x
    have hre : ∀ z, κ.val.val z = ((κ.val.val z).re : ℂ) := fun z =>
      Complex.ext (by simp) (by simp [(hκ z).2])
    have h : average ν κ x =
        ((∫ k : standardInfiniteCompact K n, (κ.val.val (k.val⁻¹ * x * k.val)).re ∂ν : ℝ) : ℂ) := by
      rw [average, ← integral_complex_ofReal]
      congr 1
      funext k
      exact hre _
    show 0 ≤ (average ν κ x).re ∧ (average ν κ x).im = 0
    rw [h, Complex.ofReal_re, Complex.ofReal_im]
    exact ⟨integral_nonneg fun k => (hκ _).1, rfl⟩
  · -- inverse-kernel integral, by compact Fubini and conjugation invariance of `μ`
    show ∫ x, average ν κ x⁻¹ ∂μ = ∫ x, κ.val.val x⁻¹ ∂μ
    have hcont : Continuous (fun p : InfiniteAdelicGL K n × standardInfiniteCompact K n =>
        κ.val.val (p.2.val⁻¹ * p.1⁻¹ * p.2.val)) := by
      have := continuous K n κ.val
      fun_prop
    have hsupp : HasCompactSupport (fun p : InfiniteAdelicGL K n × standardInfiniteCompact K n =>
        κ.val.val (p.2.val⁻¹ * p.1⁻¹ * p.2.val)) := by
      apply HasCompactSupport.intro ((isCompact_saturation κ).inv.prod isCompact_univ)
      rintro ⟨x, k⟩ hxk
      apply image_eq_zero_of_notMem_tsupport
      intro hy
      apply hxk
      refine ⟨?_, mem_univ _⟩
      show x⁻¹ ∈ saturation κ
      exact ⟨k, _, hy, by group⟩
    have hswap := integral_integral_swap_of_hasCompactSupport
      (f := fun (x : InfiniteAdelicGL K n) (k : standardInfiniteCompact K n) =>
        κ.val.val (k.val⁻¹ * x⁻¹ * k.val)) hcont hsupp (μ := μ) (ν := ν)
    have hinner : ∀ k : standardInfiniteCompact K n,
        ∫ x, κ.val.val (k.val⁻¹ * x⁻¹ * k.val) ∂μ = ∫ x, κ.val.val x⁻¹ ∂μ := by
      intro k
      have hφ : HasCompactSupport (fun y : InfiniteAdelicGL K n => κ.val.val y⁻¹) :=
        (smoothCompactKernel_hasCompactSupport K n κ).comp_homeomorph
          (Homeomorph.inv (InfiniteAdelicGL K n))
      have := integral_conj_of_mem_compact μ (standardInfiniteCompact K n)
        (isCompact_standardInfiniteCompact K n) k.property hφ
      simpa only [mul_inv_rev, inv_inv, mul_assoc] using this
    unfold average
    rw [hswap]
    simp only [hinner, integral_const, probReal_univ, one_smul]

end Langlands.Global.ArchimedeanGL
