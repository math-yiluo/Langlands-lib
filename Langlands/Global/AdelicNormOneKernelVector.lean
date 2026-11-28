import Langlands.Global.AdelicNormOnePartialConvolution

/-! # Kernel vectors of norm-one partial convolutions -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory Filter Set
open scoped CategoryTheory.MonObj CompactlySupported Pointwise

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  PositiveRealTorus RepresentationGrowth

variable {F : Type u} [Field F] [NumberField F] {H : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine H.X.left] [LocallyOfFiniteType H.X.hom]
  (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ H)
  (hi : Function.Injective (characterRestrict i)) [(characterRestrict i).range.FiniteIndex]
  (I : Type u) [Fintype I] (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I)
  (hc : IsCentral i)

local notation "A" => AdelicGroupPoints F H
local notation "A₁" => normOneSubgroup F H
local notation "Q" => PositiveRationalQuotient F H T i
local notation "q" => LeftCosetSpace.mk (positiveRationalSubgroup F H T i)
local notation "Γ" => positiveRationalSubgroup F H T i
local notation "dq" => positiveRationalQuotientHaarMeasure F H T i
local notation "dg" => (Measure.haar : Measure A)
local notation "dΓ" => positiveRationalSubgroupHaarMeasure F H T i hi I e hc
local notation "V" => Lp ℂ 2 dq
local notation "Pos" => intrinsicSubgroup F T
local notation "νP" => normalizedPositiveHaarMeasure F H T i hi I e hc

/-- The right translate `z ↦ K(z y)` of a compactly supported continuous function. -/
def rightTranslateCc (K : C_c(A, ℂ)) (y : A) : C_c(A, ℂ) :=
  ⟨⟨fun z => K (z * y), K.continuous.comp (continuous_id.mul continuous_const)⟩,
    K.hasCompactSupport.comp_homeomorph (Homeomorph.mulRight y)⟩

omit [LocallyOfFiniteType H.X.hom] in
/-- Evaluation of a right translate. -/
@[simp] theorem rightTranslateCc_apply (K : C_c(A, ℂ)) (y z : A) :
    rightTranslateCc K y z = K (z * y) := rfl

include hi e hc in
/-- A continuous compactly supported function on the positive points with nonzero integral. -/
theorem exists_positiveBump : ∃ ρ : C_c(Pos, ℂ), (∫ b, ρ b ∂νP) ≠ 0 := by
  let := positiveIsTopologicalGroup F T I e
  let := positiveLocallyCompactSpace F T I e
  let := positiveSecondCountableTopology F T I e
  let := normalizedPositiveHaarMeasure_isHaarMeasure F H T i hi I e hc
  obtain ⟨f₀, hf₀c, hf₀n, hf₀1⟩ := exists_continuous_nonneg_pos (1 : Pos)
  refine ⟨⟨⟨fun b => (f₀ b : ℂ), Complex.continuous_ofReal.comp f₀.continuous⟩,
    hf₀c.comp_left Complex.ofReal_zero⟩, ?_⟩
  have hpos : 0 < ∫ b, f₀ b ∂νP :=
    f₀.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero hf₀c hf₀n hf₀1
  change (∫ b, ((f₀ b : ℝ) : ℂ) ∂νP) ≠ 0
  rw [integral_complex_ofReal]
  exact_mod_cast hpos.ne'

variable [(Measure.haar : Measure (normOneSubgroup F H)).IsMulRightInvariant]

include hi e hc in
/-- The norm-one partial convolution at `1` is an integral over `H(𝔸)` against
`normOneSmoothingKernel`, with an integrable integrand. -/
theorem normOnePartialConvolution_one_eq_integral (ρ : C_c(Pos, ℂ)) (hρ : (∫ b, ρ b ∂νP) ≠ 0)
    (K : C_c(A, ℂ)) (h : V) :
    Integrable (fun a => normOneSmoothingKernel T i hi I e K ρ a * (h : Q → ℂ) (q a)) dg ∧
      normOnePartialConvolution T i K h 1 = (∫ b, ρ b ∂νP)⁻¹ *
        ∫ a, normOneSmoothingKernel T i hi I e K ρ a * (h : Q → ℂ) (q a) ∂dg := by
  let := positiveRationalQuotient_borelSpace F H T i hi I e hc
  let := positiveRationalQuotientHaarMeasure_isLocallyFiniteMeasure F H T i hi I e hc
  let := positiveRationalSubgroupHaarMeasure_isHaarMeasure F H T i hi I e hc
  let := positiveRationalSubgroupHaarMeasure_sigmaFinite F H T i hi I e hc
  let := positiveRationalSubgroupHaarMeasure_isMulRightInvariant F H T i hi I e hc
  obtain ⟨w, -, hk, -⟩ := Langlands.QuotientIntegration.quotientConvolutionKernel Γ
    (isClosed_positiveRationalSubgroup F H T i hi I e hc) dΓ dg dq
    (positiveRationalQuotientHaarMeasure_isCompatible F H T i hi I e hc)
    (normOneSmoothingKernel T i hi I e K ρ)
  have hint := (hk 1 h).1
  simp only [one_mul] at hint
  refine ⟨hint, ?_⟩
  have hcmp := positiveQuotientLpSmoothing_normOneSmoothingKernel T i hi I e hc K ρ h 1
  have h1 : ((1 : A₁) : A) = 1 := rfl
  rw [h1] at hcmp
  rw [eq_inv_mul_iff_mul_eq₀ hρ, ← hcmp]
  unfold positiveQuotientLpSmoothing rightConvolution
  simp only [Function.comp_apply, one_mul]

include hi e hc in
/-- Kernel vectors with a sup-norm bound: for a compact `D ⊆ H(𝔸)` there is `C ≥ 0` such that
every compactly supported continuous `K` with support in `D` and `‖K‖ ≤ M` has a vector `v` with
`⟪v, h⟫ = normOnePartialConvolution T i K h 1` for every `L²` class `h`, and `‖v‖ ≤ C M`. -/
theorem exists_kernelVector_bound (D : Set A) (hD : IsCompact D) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ K : C_c(A, ℂ), tsupport K ⊆ D → ∀ M : ℝ, (∀ z, ‖K z‖ ≤ M) →
      ∃ v : V, (∀ h : V, inner ℂ v h = normOnePartialConvolution T i K h 1) ∧ ‖v‖ ≤ C * M := by
  let := positiveIsTopologicalGroup F T I e
  let := positiveLocallyCompactSpace F T I e
  let := positiveSecondCountableTopology F T I e
  let := positiveRationalQuotient_borelSpace F H T i hi I e hc
  let := positiveRationalQuotientHaarMeasure_isLocallyFiniteMeasure F H T i hi I e hc
  let := positiveRationalSubgroupHaarMeasure_isHaarMeasure F H T i hi I e hc
  let := positiveRationalSubgroupHaarMeasure_sigmaFinite F H T i hi I e hc
  let := positiveRationalSubgroupHaarMeasure_isMulRightInvariant F H T i hi I e hc
  obtain ⟨ρ, hρ⟩ := exists_positiveBump T i hi I e hc
  obtain ⟨Mρ, hMρ⟩ := ρ.continuous.bounded_above_of_compact_support ρ.hasCompactSupport
  set D₁ : Set A₁ := {n | (n : A)⁻¹ ∈ D} with hD₁
  have hD₁c : IsCompact D₁ := by
    have hemb : Topology.IsClosedEmbedding (fun n : A₁ => (n : A)⁻¹) :=
      (Homeomorph.inv A).isClosedEmbedding.comp
        (isClosed_normOneSubgroup F H).isClosedEmbedding_subtypeVal
    exact hemb.isCompact_preimage hD
  set S : Set A := normOneDecomposition F H T i hi I e '' (tsupport ρ ×ˢ D₁) with hSdef
  have hSc : IsCompact S :=
    (ρ.hasCompactSupport.prod hD₁c).image (normOneDecomposition F H T i hi I e).continuous
  have hSS : IsCompact (S * S⁻¹) := hSc.mul hSc.inv
  have hΓS : IsCompact (Subtype.val ⁻¹' (S * S⁻¹) : Set Γ) :=
    (isClosed_positiveRationalSubgroup F H T i hi I e hc).isClosedEmbedding_subtypeVal.isCompact_preimage
      hSS
  set mD : ℝ := (dΓ).real (Subtype.val ⁻¹' (S * S⁻¹)) with hmD
  have hmD0 : 0 ≤ mD := measureReal_nonneg
  have hS0 : 0 ≤ (dg).real S := measureReal_nonneg
  set C : ℝ := ‖(∫ b, ρ b ∂νP)⁻¹‖ * max Mρ 0 * Real.sqrt ((dg).real S * mD) with hCdef
  refine ⟨C, by positivity, fun K hK M hM => ?_⟩
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 1)
  set f := normOneSmoothingKernel T i hi I e K ρ with hfdef
  have hfS : ∀ a, a ∉ S → f a = 0 := by
    intro a ha
    have hdec := positivePointMap_mul_normOneFactor F H T i hi I e a
    by_cases hρa : positiveFactor F H T i hi I e a ∈ tsupport ρ
    · by_cases hKa : ((normOneFactor F H T i hi I e a : A))⁻¹ ∈ tsupport K
      · exact absurd ⟨(_, _), ⟨hρa, hK hKa⟩, hdec⟩ ha
      · change ρ _ * starRingEnd ℂ (K _) = 0
        rw [image_eq_zero_of_notMem_tsupport hKa, map_zero, mul_zero]
    · change ρ _ * starRingEnd ℂ (K _) = 0
      rw [image_eq_zero_of_notMem_tsupport hρa, zero_mul]
  have htf : tsupport f ⊆ S :=
    closure_minimal (fun a ha => by_contra fun h => ha (hfS a h)) hSc.isClosed
  obtain ⟨w, -, hk, hbd⟩ := Langlands.QuotientIntegration.quotientConvolutionKernel Γ
    (isClosed_positiveRationalSubgroup F H T i hi I e hc) dΓ dg dq
    (positiveRationalQuotientHaarMeasure_isCompatible F H T i hi I e hc) f
  set c : ℝ := max Mρ 0 * M with hcdef
  have hc0 : 0 ≤ c := mul_nonneg (le_max_right _ _) hM0
  have hfM : ∀ a, ‖f a‖ ≤ c := by
    intro a
    change ‖ρ _ * starRingEnd ℂ (K _)‖ ≤ _
    rw [norm_mul, Complex.norm_conj]
    exact mul_le_mul ((hMρ _).trans (le_max_left _ _)) (hM _) (norm_nonneg _) (le_max_right _ _)
  have hw := hbd 1 c hfM
  have hind : Integrable (S.indicator fun _ => c) dg :=
    (integrableOn_const hSc.measure_lt_top.ne).integrable_indicator hSc.measurableSet
  have hint : ∫ a, ‖f a‖ ∂dg ≤ c * (dg).real S := by
    calc ∫ a, ‖f a‖ ∂dg ≤ ∫ a, S.indicator (fun _ => c) a ∂dg := by
          refine integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _) hind
            (Eventually.of_forall fun a => ?_)
          dsimp only
          by_cases ha : a ∈ S
          · rw [indicator_of_mem ha]; exact hfM a
          · rw [indicator_of_notMem ha, hfS a ha, norm_zero]
      _ = c * (dg).real S := by
          rw [integral_indicator_const _ hSc.measurableSet, smul_eq_mul, mul_comm]
  have hmeas : (dΓ).real (Subtype.val ⁻¹'
      ((fun s => (1 : A) * s * (1 : A)⁻¹) '' (tsupport f * (tsupport f)⁻¹))) ≤ mD := by
    refine measureReal_mono (fun x hx => ?_) hΓS.measure_lt_top.ne
    obtain ⟨s, hs, hsx⟩ := hx
    change (x : A) ∈ S * S⁻¹
    rw [← hsx]
    simp only [one_mul, inv_one, mul_one]
    exact Set.mul_subset_mul htf (Set.inv_subset_inv.mpr htf) hs
  have hw2 : ‖w 1‖ ^ 2 ≤ c ^ 2 * ((dg).real S * mD) := by
    calc ‖w 1‖ ^ 2 ≤ c * (∫ a, ‖f a‖ ∂dg) * (dΓ).real (Subtype.val ⁻¹'
          ((fun s => (1 : A) * s * (1 : A)⁻¹) '' (tsupport f * (tsupport f)⁻¹))) := hw
      _ ≤ c * (c * (dg).real S) * mD := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left hint hc0) hmeas measureReal_nonneg
            (mul_nonneg hc0 (mul_nonneg hc0 hS0))
      _ = c ^ 2 * ((dg).real S * mD) := by ring
  have hw1 : ‖w 1‖ ≤ c * Real.sqrt ((dg).real S * mD) := by
    have h := Real.abs_le_sqrt hw2
    rw [abs_of_nonneg (norm_nonneg _), Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc0] at h
    exact h
  refine ⟨starRingEnd ℂ (∫ b, ρ b ∂νP)⁻¹ • w 1, fun h => ?_, ?_⟩
  · rw [inner_smul_left, Complex.conj_conj, (hk 1 h).2,
      (normOnePartialConvolution_one_eq_integral T i hi I e hc ρ hρ K h).2]
    simp only [one_mul]
    rfl
  · rw [norm_smul, Complex.norm_conj]
    calc ‖(∫ b, ρ b ∂νP)⁻¹‖ * ‖w 1‖ ≤ ‖(∫ b, ρ b ∂νP)⁻¹‖ * (c * Real.sqrt ((dg).real S * mD)) :=
          mul_le_mul_of_nonneg_left hw1 (norm_nonneg _)
      _ = C * M := by rw [hCdef, hcdef]; ring

include hi e hc in
/-- Every norm-one partial convolution at `1` with a compactly supported continuous kernel is an
inner product with a vector of `L²`. -/
theorem exists_inner_eq_normOnePartialConvolution (K : C_c(A, ℂ)) :
    ∃ v : V, ∀ h : V, inner ℂ v h = normOnePartialConvolution T i K h 1 := by
  obtain ⟨C, -, hC⟩ := exists_kernelVector_bound T i hi I e hc (tsupport K) K.hasCompactSupport
  obtain ⟨M, hM⟩ := K.continuous.bounded_above_of_compact_support K.hasCompactSupport
  obtain ⟨v, hv, -⟩ := hC K subset_rfl M hM
  exact ⟨v, hv⟩

/-- The kernel vector of `K`: the `L²` class `v` with `⟪v, h⟫ = normOnePartialConvolution T i K h 1`
for every `h`. -/
def normOneKernelVector (K : C_c(A, ℂ)) : V :=
  Classical.choose (exists_inner_eq_normOnePartialConvolution T i hi I e hc K)

/-- The defining property of the kernel vector. -/
theorem inner_normOneKernelVector (K : C_c(A, ℂ)) (h : V) :
    inner ℂ (normOneKernelVector T i hi I e hc K) h = normOnePartialConvolution T i K h 1 :=
  Classical.choose_spec (exists_inner_eq_normOnePartialConvolution T i hi I e hc K) h

/-- Uniqueness of the kernel vector. -/
theorem normOneKernelVector_eq (K : C_c(A, ℂ)) (v : V)
    (hv : ∀ h : V, inner ℂ v h = normOnePartialConvolution T i K h 1) :
    normOneKernelVector T i hi I e hc K = v :=
  ext_inner_right ℂ fun h => by rw [inner_normOneKernelVector, hv]

/-- The kernel vectors of kernels supported in a fixed compact set are bounded by a multiple of
the sup norm. -/
theorem exists_norm_normOneKernelVector_le (D : Set A) (hD : IsCompact D) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ K : C_c(A, ℂ), tsupport K ⊆ D → ∀ M : ℝ, (∀ z, ‖K z‖ ≤ M) →
      ‖normOneKernelVector T i hi I e hc K‖ ≤ C * M := by
  obtain ⟨C, hC0, hC⟩ := exists_kernelVector_bound T i hi I e hc D hD
  refine ⟨C, hC0, fun K hK M hM => ?_⟩
  obtain ⟨v, hv, hvC⟩ := hC K hK M hM
  rw [normOneKernelVector_eq T i hi I e hc K v hv]
  exact hvC

/-- Norm-one partial convolutions at any point are inner products with kernel vectors of right
translates. -/
theorem normOnePartialConvolution_eq_inner (K : C_c(A, ℂ)) (h : V) (y : A) :
    normOnePartialConvolution T i K h y =
      inner ℂ (normOneKernelVector T i hi I e hc (rightTranslateCc K y)) h := by
  rw [inner_normOneKernelVector]
  have h1 := normOnePartialConvolution_mul_right T i K h 1 y
  rw [one_mul] at h1
  exact h1

/-- Kernel vectors are additive under differences of kernels. -/
theorem normOneKernelVector_sub (K₁ K₂ : C_c(A, ℂ)) :
    normOneKernelVector T i hi I e hc (K₁ - K₂) =
      normOneKernelVector T i hi I e hc K₁ - normOneKernelVector T i hi I e hc K₂ := by
  obtain ⟨ρ, hρ⟩ := exists_positiveBump T i hi I e hc
  refine normOneKernelVector_eq T i hi I e hc _ _ fun h => ?_
  rw [inner_sub_left, inner_normOneKernelVector, inner_normOneKernelVector]
  obtain ⟨hi₁, e₁⟩ := normOnePartialConvolution_one_eq_integral T i hi I e hc ρ hρ K₁ h
  obtain ⟨hi₂, e₂⟩ := normOnePartialConvolution_one_eq_integral T i hi I e hc ρ hρ K₂ h
  obtain ⟨-, e₃⟩ := normOnePartialConvolution_one_eq_integral T i hi I e hc ρ hρ (K₁ - K₂) h
  rw [e₁, e₂, e₃, ← mul_sub, ← integral_sub hi₁ hi₂]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun a => ?_)
  change ρ _ * starRingEnd ℂ (K₁ _) * _ - ρ _ * starRingEnd ℂ (K₂ _) * _ =
    ρ _ * starRingEnd ℂ ((K₁ - K₂) _) * _
  rw [CompactlySupportedContinuousMap.coe_sub, Pi.sub_apply, map_sub]
  ring

/-- Lipschitz bound for kernel vectors of kernels supported in a fixed compact set. -/
theorem exists_norm_normOneKernelVector_sub_le (D : Set A) (hD : IsCompact D) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ K₁ K₂ : C_c(A, ℂ), tsupport K₁ ⊆ D → tsupport K₂ ⊆ D → ∀ M : ℝ,
      (∀ z, ‖K₁ z - K₂ z‖ ≤ M) →
      ‖normOneKernelVector T i hi I e hc K₁ - normOneKernelVector T i hi I e hc K₂‖ ≤ C * M := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_normOneKernelVector_le T i hi I e hc D hD
  refine ⟨C, hC0, fun K₁ K₂ h₁ h₂ M hM => ?_⟩
  rw [← normOneKernelVector_sub]
  refine hC _ ((tsupport_sub _ _).trans (union_subset h₁ h₂)) M fun z => ?_
  rw [CompactlySupportedContinuousMap.coe_sub, Pi.sub_apply]
  exact hM z

/-- A family of kernels that is jointly continuous, with locally uniformly compact supports, has
continuously varying kernel vectors. -/
theorem continuous_normOneKernelVector_comp {P : Type*} [TopologicalSpace P]
    (Fk : P → C_c(A, ℂ)) (hF : Continuous fun x : P × A => Fk x.1 x.2)
    (hD : ∀ p₀ : P, ∃ U ∈ nhds p₀, ∃ D : Set A, IsCompact D ∧ ∀ p ∈ U, tsupport (Fk p) ⊆ D) :
    Continuous fun p => normOneKernelVector T i hi I e hc (Fk p) := by
  rw [continuous_iff_continuousAt]
  intro p₀
  obtain ⟨U, hU, D, hDc, hDU⟩ := hD p₀
  obtain ⟨C, hC0, hC⟩ := exists_norm_normOneKernelVector_sub_le T i hi I e hc D hDc
  have : CompactSpace D := isCompact_iff_compactSpace.mp hDc
  let g : P → C(D, ℂ) := fun p =>
    (ContinuousMap.curry (⟨fun x : P × A => Fk x.1 x.2, hF⟩ : C(P × A, ℂ)) p).restrict D
  have hg : Continuous g :=
    (ContinuousMap.continuous_restrict D).comp (ContinuousMap.curry _).continuous
  refine Metric.tendsto_nhds.mpr fun ε hε => ?_
  set τ : ℝ := ε / (C + 1) with hτdef
  have hτpos : 0 < τ := div_pos hε (by linarith)
  filter_upwards [Metric.tendsto_nhds.mp hg.continuousAt τ hτpos, hU] with p hp hpU
  have hpt : ∀ z, ‖Fk p z - Fk p₀ z‖ ≤ τ := by
    intro z
    by_cases hz : z ∈ D
    · have h1 := ContinuousMap.norm_coe_le_norm (g p - g p₀) ⟨z, hz⟩
      rw [← dist_eq_norm] at h1
      exact h1.trans hp.le
    · rw [image_eq_zero_of_notMem_tsupport (fun h => hz (hDU p hpU h)),
        image_eq_zero_of_notMem_tsupport (fun h => hz (hDU p₀ (mem_of_mem_nhds hU) h)),
        sub_zero, norm_zero]
      exact hτpos.le
  rw [dist_eq_norm]
  calc ‖normOneKernelVector T i hi I e hc (Fk p) - normOneKernelVector T i hi I e hc (Fk p₀)‖
      ≤ C * τ := hC _ _ (hDU p hpU) (hDU p₀ (mem_of_mem_nhds hU)) τ hpt
    _ < ε := by
      rw [hτdef, mul_div_assoc']
      rw [div_lt_iff₀ (by linarith)]
      nlinarith

end Langlands.Global
