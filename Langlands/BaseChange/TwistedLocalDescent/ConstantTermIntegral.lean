import Langlands.BaseChange.TwistedLocalDescent.ConstantTerm
import Langlands.BaseChange.TwistedLocalDescent.MassReduction
import Langlands.BaseChange.TwistedLocalDescent.LocalHelpers

/-! # The integral of the twisted constant term over a subset of the Levi

Let `μM` be a Haar measure on the Levi `M(E)`, `μU` a Haar measure on the radical
`B.unipotentSubgroup E` giving `U ∩ K` volume one, and `μK` the Haar probability measure on
`K = GL_n(𝒪_E)`. For a measurable subset `S` of `M(E)`, the integral over `S` of the normalized
twisted constant term `φ^{P,σ}` (`normalizedTwistedParabolicConstantTerm`) equals the integral
over `K` of the twisted orbital kernel `Φ(κ) = ∫_P 1_S(p_M) δ_P(p)^{1/2} φ(κ⁻¹ p σ(κ)) dp`, with
`dp = dm du`. See the paired Markdown.
-/

noncomputable section

namespace Langlands.BaseChange.TwistedLocalDescent

open MeasureTheory Measure Set
open Langlands.GeneralLinear Langlands.HarmonicAnalysis TwistedVanDijk
open scoped ENNReal NNReal

universe u v

variable {F : Type u} [Field F] [TopologicalSpace F]
  {E : Type v} [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra F E] [IsModuleTopology F E] (σ : E ≃ₐ[F] E) {n : ℕ} (B : BlockShape n)

attribute [local instance] LocalFieldTopology.t2Space
  LocalFieldTopology.generalLinear_t2Space
  LocalFieldTopology.generalLinear_locallyCompactSpace
  LocalFieldTopology.generalLinear_secondCountableTopology
  unipotentSubgroup_secondCountable unipotentSubgroup_locallyCompact
  parabolic_secondCountable parabolic_locallyCompact integralGL_compactSpace
  integralGL_secondCountable

variable [MeasurableSpace (GeneralLinear n E)] [BorelSpace (GeneralLinear n E)]
  [MeasurableSpace (B.Levi E)] [BorelSpace (B.Levi E)]
  (μM : Measure (B.Levi E)) [μM.IsHaarMeasure]
  (μU : Measure (B.unipotentSubgroup E)) [μU.IsHaarMeasure]
  (μK : Measure (integralGL E n)) [μK.IsHaarMeasure] [IsProbabilityMeasure μK]

/-- **The Levi integral of the twisted constant term over `S` as a `K`-integral.** -/
theorem integral_indicator_twistedConstantTerm
    (hU : μU {y | (y : GeneralLinear n E) ∈ integralGL E n} = 1) (S : Set (B.Levi E))
    (hS : MeasurableSet S) (φ : SchwartzBruhat (GeneralLinear n E)) :
    ∫ x, S.indicator (normalizedTwistedParabolicConstantTerm E B σ φ) x ∂μM =
      ∫ k, twistedOrbitalKernel (Matrix.GeneralLinearGroup.map (σ : E →+* E))
        (parabolicHaar B μM μU) {p | B.leviProjection E p ∈ S}
        (fun p => (parabolicHalfModulusNNReal B p : ℝ)) φ k ∂μK := by
  set θ := Matrix.GeneralLinearGroup.map (n := Fin n) (σ : E →+* E)
  set δr : B.Levi E → ℝ := fun m =>
    (NNReal.sqrt ((LocalFieldData.ofInstances E).leviModulus B m : ℝ≥0) : ℝ)
  have hδr : Continuous δr := by
    have h := (NNReal.continuous_coe.comp (continuous_parabolicHalfModulusNNReal (E := E) B)).comp
      (B.leviInParabolicContinuous E).continuous
    refine h.congr fun m => ?_
    change ((NNReal.sqrt ((LocalFieldData.ofInstances E).leviModulus B
      (B.leviProjection E (B.leviInParabolic E m)) : ℝ≥0) : ℝ≥0) : ℝ) = δr m
    rw [B.leviProjection_section E m]
  set f : (B.Levi E × B.unipotentSubgroup E) × integralGL E n → ℂ := fun z =>
    S.indicator (fun m => (δr m : ℂ)) z.1.1 *
      φ ((z.2 : GeneralLinear n E)⁻¹ * B.leviEmbedding E z.1.1 * (z.1.2 : GeneralLinear n E) *
        θ z.2)
  set g : (B.Levi E × B.unipotentSubgroup E) × integralGL E n → ℂ := fun z =>
    (δr z.1.1 : ℂ) *
      φ ((z.2 : GeneralLinear n E)⁻¹ * B.leviEmbedding E z.1.1 * (z.1.2 : GeneralLinear n E) *
        θ z.2)
  have hθc : Continuous θ := continuous_entrywiseAut σ n
  have hargc : Continuous fun z : (B.Levi E × B.unipotentSubgroup E) × integralGL E n =>
      (z.2 : GeneralLinear n E)⁻¹ * B.leviEmbedding E z.1.1 * (z.1.2 : GeneralLinear n E) *
        θ z.2 :=
    (((continuous_subtype_val.comp continuous_snd).inv.mul
      ((B.leviEmbeddingContinuous E).continuous.comp (continuous_fst.comp continuous_fst))).mul
      (continuous_subtype_val.comp (continuous_snd.comp continuous_fst))).mul
      (hθc.comp (continuous_subtype_val.comp continuous_snd))
  have hgc : Continuous g :=
    (Complex.continuous_ofReal.comp (hδr.comp (continuous_fst.comp continuous_fst))).mul
      (φ.continuous.comp hargc)
  -- compact support of `g`
  set C : Set (GeneralLinear n E) := (fun q : GeneralLinear n E × GeneralLinear n E =>
    q.1 * q.2 * (θ q.1)⁻¹) '' ((integralGL E n : Set (GeneralLinear n E)) ×ˢ tsupport φ)
  have hC : IsCompact C := ((isCompact_integralGL n).prod φ.hasCompactSupport).image
    ((continuous_fst.mul continuous_snd).mul (hθc.comp continuous_fst).inv)
  have hPC : IsCompact {p : B.parabolic E | (p : GeneralLinear n E) ∈ C} :=
    (B.isClosed_parabolic E).isClosedEmbedding_subtypeVal.isCompact_preimage hC
  have hMU : IsCompact ((parabolicProductHomeomorph (R := E) B) ⁻¹'
      {p : B.parabolic E | (p : GeneralLinear n E) ∈ C}) :=
    (parabolicProductHomeomorph (R := E) B).isCompact_preimage.mpr hPC
  have hgs : HasCompactSupport g := by
    refine HasCompactSupport.intro (hMU.prod isCompact_univ) fun z hz => ?_
    by_contra hne
    apply hz
    refine ⟨?_, mem_univ _⟩
    have hφne : φ ((z.2 : GeneralLinear n E)⁻¹ * B.leviEmbedding E z.1.1 *
        (z.1.2 : GeneralLinear n E) * θ z.2) ≠ 0 := right_ne_zero_of_mul hne
    refine ⟨((z.2 : GeneralLinear n E), (z.2 : GeneralLinear n E)⁻¹ * B.leviEmbedding E z.1.1 *
      (z.1.2 : GeneralLinear n E) * θ z.2), ⟨z.2.property, subset_tsupport φ hφne⟩, ?_⟩
    change (z.2 : GeneralLinear n E) * ((z.2 : GeneralLinear n E)⁻¹ * B.leviEmbedding E z.1.1 *
      (z.1.2 : GeneralLinear n E) * θ z.2) * (θ z.2)⁻¹ =
        B.leviEmbedding E z.1.1 * (z.1.2 : GeneralLinear n E)
    group
  have hgint : Integrable g ((μM.prod μU).prod μK) := hgc.integrable_of_hasCompactSupport hgs
  have hfm : Measurable f := by
    refine Measurable.mul ?_ (φ.continuous.comp hargc).measurable
    exact ((Complex.measurable_ofReal.comp hδr.measurable).indicator hS).comp
      (measurable_fst.comp measurable_fst)
  have hfint : Integrable f ((μM.prod μU).prod μK) := by
    refine hgint.mono hfm.aestronglyMeasurable (Filter.Eventually.of_forall fun z => ?_)
    simp only [f, g, norm_mul]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    by_cases hz : z.1.1 ∈ S
    · rw [Set.indicator_of_mem hz]
    · rw [Set.indicator_of_notMem hz, norm_zero]
      exact norm_nonneg _
  -- the left side
  have hL : ∫ x, S.indicator (normalizedTwistedParabolicConstantTerm E B σ φ) x ∂μM =
      ∫ z, f z ∂((μM.prod μU).prod μK) := by
    rw [integral_prod f hfint, integral_prod _ hfint.integral_prod_left]
    congr 1
    funext m
    by_cases hm : m ∈ S
    · rw [Set.indicator_of_mem hm,
        normalizedTwistedParabolicConstantTerm_apply_unipotentSubgroup σ B μU hU μK]
      simp only [f, Set.indicator_of_mem hm, integral_const_mul]
      congr 1
    · rw [Set.indicator_of_notMem hm]
      simp only [f, Set.indicator_of_notMem hm, zero_mul, integral_zero]
  -- the right side
  have hR : ∀ κ : integralGL E n, twistedOrbitalKernel θ (parabolicHaar B μM μU)
      {p | B.leviProjection E p ∈ S} (fun p => (parabolicHalfModulusNNReal B p : ℝ)) φ κ =
      ∫ q, f (q, κ) ∂(μM.prod μU) := by
    intro κ
    unfold twistedOrbitalKernel parabolicHaar
    have hQm : MeasurableSet {p : B.parabolic E | B.leviProjection E p ∈ S} :=
      hS.preimage (B.leviProjectionContinuous E).continuous.measurable
    have hFm : Measurable fun p : B.parabolic E =>
        {p : B.parabolic E | B.leviProjection E p ∈ S}.indicator
          (fun p => ((parabolicHalfModulusNNReal B p : ℝ) : ℂ) *
            φ ((κ : GeneralLinear n E)⁻¹ * p * θ κ)) p := by
      refine Measurable.indicator ?_ hQm
      exact ((Complex.continuous_ofReal.comp (NNReal.continuous_coe.comp
        (continuous_parabolicHalfModulusNNReal (E := E) B))).mul (φ.continuous.comp
          ((continuous_const.mul continuous_subtype_val).mul continuous_const))).measurable
    rw [integral_map (measurable_parabolicProduct B).aemeasurable hFm.aestronglyMeasurable]
    congr 1
    funext q
    have hpr : B.leviProjection E (parabolicProduct B q) = q.1 :=
      leviProjection_parabolicProduct B q
    by_cases hq : q.1 ∈ S
    · rw [Set.indicator_of_mem (show parabolicProduct B q ∈
        {p : B.parabolic E | B.leviProjection E p ∈ S} by simpa [hpr] using hq)]
      simp only [f, Set.indicator_of_mem hq]
      congr 1
      · simp only [parabolicHalfModulusNNReal, MonoidHom.coe_mk, OneHom.coe_mk, hpr, δr]
      · simp only [coe_parabolicProduct]
        group
    · rw [Set.indicator_of_notMem (show parabolicProduct B q ∉
        {p : B.parabolic E | B.leviProjection E p ∈ S} by simpa [hpr] using hq)]
      simp only [f, Set.indicator_of_notMem hq, zero_mul]
  simp_rw [hR]
  rw [hL, integral_prod_symm f hfint]

end Langlands.BaseChange.TwistedLocalDescent
