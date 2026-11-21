import Langlands.Global.RankinSelberg.RealPrincipalSeriesWhittakerUniqueness
import Langlands.Global.RankinSelberg.RealGodementOpenCellModel
import Langlands.Analysis.SeveralComplex.ParametricIntegral

/-! # The real Jacquet distribution on the strict chamber and the reversal cell -/

noncomputable section

open Filter Function Set MeasureTheory TopologicalSpace
open Langlands.Archimedean Langlands.GeneralLinear Langlands.HarmonicAnalysis
open Langlands.LocalFactor.Archimedean Langlands.Whittaker
open scoped ContDiff Distributions Matrix.Norms.Operator Pointwise

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealJacquetTestDistribution

open RealGodement RealBorelTestAverage RealBorelRightHaar RealPrincipalSeriesDistribution
open RealPrincipalSeriesWhittakerUniqueness RealBruhatDistributionRestriction
open RealWhittakerTranslationDistribution RealJacquetFrobenius
open GramFormula PartialJacquet RealInducedStandardBound
open ArchimedeanLocal

variable {r : ℕ}
local notation "M" => Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ
local notation "G" => Langlands.GeneralLinear (r + 1) ℝ
local notation "B" => upperTriangularSubgroup (r + 1) ℝ
local notation "U" => Langlands.GeneralLinear.upperUnipotent (r + 1) ℝ
local notation "H" => U × B
local notation "W" => weylLong (r + 1) ℝ
local notation "O" => longestBruhatCell ℝ r
local notation "P" => (Fin (r + 1) → ℂ)
local notation "Signs" => (Fin (r + 1) → Fin 2)
local notation "dx" => rightBorelMeasure r
local notation "p₀(" K ")" => ContDiffMapSupportedIn.supSeminorm ℝ M ℝ ⊤ K 0

local instance : MeasurableSpace B := borel B
local instance : BorelSpace B := ⟨rfl⟩
local instance : MeasurableSpace U := borel U
local instance : BorelSpace U := ⟨rfl⟩
local instance : LocallyCompactSpace G := Units.isOpenEmbedding_val.locallyCompactSpace
local instance : LocallyCompactSpace B := (isClosed_upperTriangularSubgroup (r + 1) ℝ).locallyCompactSpace
local instance : SecondCountableTopology M :=
  inferInstanceAs (SecondCountableTopology (Fin (r + 1) → Fin (r + 1) → ℝ))
local instance : SecondCountableTopology G :=
  (show Topology.IsOpenEmbedding (Units.val : G → M) from Units.isOpenEmbedding_val).isInducing.secondCountableTopology
local instance : SecondCountableTopology B :=
  (show Topology.IsInducing (Subtype.val : B → G) from Topology.IsInducing.subtypeVal).secondCountableTopology

/-- In the strict chamber the convergent Jacquet evaluation of the real test average. -/
def dominantDistribution (a : ℝˣ) (s : P) (e : Signs)
    (hDom : IsStrictlyDominant (realPositionExponent (normalizedCharacterBlocks s e)) r) :
    𝓓'(invertibleDomain r, ℂ) :=
  averagedDistribution s e (additiveJacquetForm a hDom) (hasCompactDerivativeBound_additiveJacquetForm a hDom)

theorem dominantDistribution_covariant (a : ℝˣ) (s : P) (e : Signs)
    (hDom : IsStrictlyDominant (realPositionExponent (normalizedCharacterBlocks s e)) r) :
    IsUnipotentWhittakerCovariant (dominantDistribution a s e hDom) (-a) := by
  apply averagedDistribution_covariant
  intro u f
  change additiveJacquetIntegral a (fun k => f.val (k * u.val)) 1 =
    realWhittakerCharacter (-a) u.val * additiveJacquetIntegral a f.val 1
  rw [additiveJacquetIntegral_rightTranslate, one_mul]
  simpa only [mul_one] using realGodementOpenCellCovariance r a f.val u 1

private theorem norm_jacquetForm_le_sup (a : ℝˣ) (s : P) (e : Signs)
    (hDom : IsStrictlyDominant (realPositionExponent (normalizedCharacterBlocks s e)) r) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ F : principalSeries ℝ (r + 1) (posChar s e), ∀ R : ℝ,
      (∀ k ∈ unitaryCompact ℝ (r + 1), ‖F.val k‖ ≤ R) → ‖additiveJacquetForm a hDom F‖ ≤ A * R := by
  let ds := normalizedCharacterBlocks s e
  let w (j : ℕ) := (realPositionExponent ds j).re
  let F₀ := expFun (r + 1) w
  have hF₀ : F₀ ∈ principalSeries ℝ (r + 1) (absChar w) := expFun_mem (r + 1) w
  have hχ := RealStrictCharacterLanglandsQuotient.isSignedPower ds
  have hχ₀ := RealLeviLimit.isSignedPower_absChar w
  have hDom₀ : IsStrictlyDominant (fun j => (w j : ℂ)) r := by
    intro j hj
    simpa only [Complex.ofReal_re, w, ds] using hDom j hj
  have hI₀ := integrable_additiveJacquetKernel_of_mem_principalSeries a hχ₀ hDom₀ hF₀ (1 : G)
  let A := ∫ u : U, ‖additiveJacquetKernel a F₀ 1 u‖ ∂upperStepHaar r a
  refine ⟨A, integral_nonneg (fun _ => norm_nonneg _), fun F R hR => ?_⟩
  have hpoint (g : G) : ‖F.val g‖ ≤ R * ‖F₀ g‖ := by
    obtain ⟨d, u, k, hk, rfl⟩ := exists_diagonalUnits_mul_upperUnipotent_mul_unitaryCompact g
    have hOne : F₀ k = 1 := by
      simpa only [one_mul, expFun_one] using expFun_mul (r + 1) w 1 hk
    have hNorm : ‖principalSeriesCharacter ℝ (r + 1) (absChar w) d‖ =
        ‖principalSeriesCharacter ℝ (r + 1) (posChar s e) d‖ := by
      change _ = ‖principalSeriesCharacter ℝ (r + 1) (realPositionCharacter ds) d‖
      rw [norm_principalSeriesCharacter hχ₀, norm_principalSeriesCharacter hχ]
      simp only [Complex.ofReal_re, w]
    rw [F.property.2, hF₀.2, hOne, mul_one, norm_mul, hNorm, mul_comm R]
    exact mul_le_mul_of_nonneg_left (hR k hk) (norm_nonneg _)
  have hI := integrable_additiveJacquetKernel_of_mem_principalSeries a hχ hDom F.property (1 : G)
  change ‖∫ u, additiveJacquetKernel a F.val 1 u ∂upperStepHaar r a‖ ≤ A * R
  calc
    _ ≤ ∫ u, ‖additiveJacquetKernel a F.val 1 u‖ ∂upperStepHaar r a := norm_integral_le_integral_norm _
    _ ≤ ∫ u, R * ‖additiveJacquetKernel a F₀ 1 u‖ ∂upperStepHaar r a :=
      integral_mono hI.norm (hI₀.norm.const_mul R) fun u => by
        simpa only [additiveJacquetKernel, norm_mul, norm_standardCharacter, mul_one] using hpoint (W * u.val)
    _ = _ := by rw [integral_const_mul, mul_comm]

private theorem norm_test_le_supSeminorm (K : Compacts M) (f : 𝓓_{K}(M, ℝ)) (x : M) :
    ‖f x‖ ≤ p₀(K) f := by
  have h := ContDiffMapSupportedIn.norm_iteratedFDeriv_apply_le_seminorm_top ℝ
    (f := f) (i := 0) (x := x)
  rw [norm_iteratedFDeriv_zero] at h
  exact h.trans ((Finset.le_sup (f := ContDiffMapSupportedIn.seminorm ℝ M ℝ ⊤ K)
    (Finset.mem_Iic.mpr (le_refl 0))) f)

private theorem exists_bound_borelAverage_on_unitary (s : P) (e : Signs)
    (K : Compacts M) (hK : (K : Set M) ⊆ invertibleDomain r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : 𝓓_{K}(M, ℝ), ∀ k ∈ unitaryCompact ℝ (r + 1),
      ‖(averageMap s e (TestFunction.postcompCLM Complex.ofRealCLM (TestFunction.ofSupportedIn hK f))).val k‖ ≤
        C * p₀(K) f := by
  let Q : Set G := unitaryCompact ℝ (r + 1)
  have hQ : IsCompact Q := isCompact_iff_compactSpace.mpr
    (RealPrincipalSeriesDuality.compactSpace_unitaryCompact (r + 1))
  let S : Set B := Subtype.val ⁻¹' ((Units.val ⁻¹' (K : Set M)) * Q⁻¹)
  have hK' : IsCompact (Units.val ⁻¹' (K : Set M) : Set G) :=
    isCompact_val_preimage K.isCompact (fun _ h => hK h)
  have hClosed := (isClosed_upperTriangularSubgroup (r + 1) ℝ).isClosedEmbedding_subtypeVal
  have hS : IsCompact S := hClosed.isCompact_preimage (hK'.mul hQ.inv)
  let weight := inverseWeight (positionBorelCharacter s e)
  have hw := continuous_inverseWeight (positionBorelCharacter s e) (continuous_positionBorelCharacter s e)
  obtain ⟨A, hA⟩ := hS.exists_bound_of_continuousOn hw.continuousOn
  refine ⟨max A 0 * (dx).real S, mul_nonneg (le_max_right _ _) ENNReal.toReal_nonneg, fun f k hk => ?_⟩
  change ‖∫ b : B, weight b * (f (b.val.val * k.val) : ℂ) ∂dx‖ ≤ _
  have hZero (b : B) (hb : b ∉ S) : weight b * (f (b.val.val * k.val) : ℂ) = 0 := by
    have hz : b.val.val * k.val ∉ K := fun h => hb ⟨b.val * k, h, k⁻¹, mem_inv.mpr hk, mul_inv_cancel_right _ _⟩
    rw [show f (b.val.val * k.val) = 0 from f.zero_on_compl hz, Complex.ofReal_zero, mul_zero]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hZero]
  let : IsFiniteMeasure ((dx).restrict S) := isFiniteMeasure_restrict.mpr hS.measure_lt_top.ne
  have hnorm : ∀ᵐ b ∂(dx).restrict S, ‖weight b * (f (b.val.val * k.val) : ℂ)‖ ≤ max A 0 * p₀(K) f :=
    ae_restrict_of_forall_mem hS.measurableSet fun b hb => by
      rw [norm_mul, Complex.norm_real]
      exact mul_le_mul ((hA b hb).trans (le_max_left _ _)) (norm_test_le_supSeminorm K f _)
        (norm_nonneg _) (le_max_right _ _)
  simpa only [Measure.real, Measure.restrict_apply_univ, mul_right_comm (max A 0)] using
    (norm_integral_le_of_norm_le_const hnorm)

/-- The strict-chamber distribution has order zero on every compact test support. -/
theorem dominantDistribution_order_zero (a : ℝˣ) (s : P) (e : Signs)
    (hDom : IsStrictlyDominant (realPositionExponent (normalizedCharacterBlocks s e)) r)
    (K : Compacts M) (hK : (K : Set M) ⊆ invertibleDomain r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f, ‖dominantDistribution a s e hDom (TestFunction.ofSupportedIn hK f)‖ ≤ C * p₀(K) f := by
  obtain ⟨A, hA, hJacquet⟩ := norm_jacquetForm_le_sup a s e hDom
  obtain ⟨D, hD, hAvg⟩ := exists_bound_borelAverage_on_unitary s e K hK
  refine ⟨A * D, mul_nonneg hA hD, fun f => ?_⟩
  simpa only [dominantDistribution, averagedDistribution_apply, mul_assoc] using
    hJacquet _ _ (hAvg f)

/-- Coordinates on the reversal cell in the order used by the Jacquet integral. -/
def jacquetOrbit (r : ℕ) :
    (Langlands.GeneralLinear.upperUnipotent (r + 1) ℝ × upperTriangularSubgroup (r + 1) ℝ) ≃ₜ
      (longestBruhatCell ℝ r : Set (Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ)) :=
  (Homeomorph.prodComm _ _).trans
    (((Homeomorph.refl _).prodCongr (Homeomorph.inv _)).trans (orbitHomeomorph (r := r)))

theorem jacquetOrbit_val (p : H) : (jacquetOrbit r p).val = (p.2.val * W * p.1.val).val := by
  change (orbitHomeomorph (p.2, p.1⁻¹)).val = _
  rw [orbitHomeomorph_val]
  simp only [matrixAction, MonoidHom.coe_mk, OneHom.coe_mk, LinearMap.comp_apply,
    LinearMap.mulRight_apply, LinearMap.mulLeft_apply, inv_inv, Units.val_mul]

private theorem longestCell_le : O ≤ invertibleDomain r := by
  rintro X ⟨g, _, rfl⟩
  exact ⟨g, rfl⟩

private theorem isCompact_jacquetOrbit_preimage {K : Set M} (hK : IsCompact K) (hKO : K ⊆ O) :
    IsCompact ((fun p : H => (jacquetOrbit r p).val) ⁻¹' K) := by
  have h := Topology.IsEmbedding.subtypeVal.isInducing.isCompact_preimage' hK
    (show K ⊆ Set.range (Subtype.val : (O : Set M) → M) by simpa using hKO)
  exact (jacquetOrbit r).isCompact_preimage.mpr h

def jacquetOrbitKernel (a : ℝˣ) (s : P) (e : Signs) (f : M → ℝ) (p : H) : ℂ :=
  inverseWeight (positionBorelCharacter s e) p.2 * (f (jacquetOrbit r p).val : ℂ) *
    (standardCharacter (realScaledCharacter a) r p.1 : ℂ)

private theorem continuous_phase (a : ℝˣ) : Continuous (fun u : U => (standardCharacter (realScaledCharacter a) r u : ℂ)) :=
  (realScaledCharacter a).continuous_complex.comp (continuous_finsetSum Finset.univ fun (i : Fin r) _ =>
    (Units.continuous_val.comp continuous_subtype_val).matrix_elem i.castSucc i.succ)

private theorem continuous_jacquetOrbitKernel (a : ℝˣ) (s : P) (e : Signs) {f : M → ℝ} (hf : Continuous f) :
    Continuous (jacquetOrbitKernel a s e f) :=
  (((continuous_inverseWeight (positionBorelCharacter s e) (continuous_positionBorelCharacter s e)).comp
      continuous_snd).mul (Complex.continuous_ofReal.comp (hf.comp
        (continuous_subtype_val.comp (jacquetOrbit r).continuous)))).mul (continuous_phase a |>.comp continuous_fst)

/-- A compact test on the reversal cell gives an integrable joint kernel at every exponent. -/
theorem integrable_jacquetOrbitKernel (a : ℝˣ) (s : P) (e : Signs) (f : 𝓓(O, ℝ)) :
    Integrable (jacquetOrbitKernel a s e f) ((upperStepHaar r a).prod dx) := by
  let : (upperStepHaar r a).IsHaarMeasure := upperStepHaar_isHaar r a
  let : SigmaFinite (upperStepHaar r a) := upperStepHaar_sigmaFinite r a
  have hC := isCompact_jacquetOrbit_preimage f.hasCompactSupport f.tsupport_subset
  apply (continuous_jacquetOrbitKernel a s e f.contDiff.continuous).integrable_of_hasCompactSupport
  refine hC.of_isClosed_subset (isClosed_tsupport _) (closure_minimal ?_ hC.isClosed)
  intro p hp
  exact not_not.mp fun hn => hp (by
    simp only [jacquetOrbitKernel, image_eq_zero_of_notMem_tsupport hn, Complex.ofReal_zero, mul_zero, zero_mul])

/-- The restriction of the dominant distribution to the reversal cell is
integration of its joint Borel and upper-unipotent kernel. -/
theorem dominantDistribution_reversalIntegral (a : ℝˣ) (s : P) (e : Signs)
    (hDom : IsStrictlyDominant (realPositionExponent (normalizedCharacterBlocks s e)) r) (f : 𝓓(O, ℝ)) :
    dominantDistribution a s e hDom (TestFunction.monoCLM ℝ f) =
      ∫ p : H, jacquetOrbitKernel a s e f p ∂((upperStepHaar r a).prod dx) := by
  let : SigmaFinite (upperStepHaar r a) := upperStepHaar_sigmaFinite r a
  rw [integral_prod _ (integrable_jacquetOrbitKernel a s e f)]
  simp only [dominantDistribution, averagedDistribution_apply, additiveJacquetForm,
    LinearMap.comp_apply, LinearMap.proj_apply]
  change additiveJacquetIntegral a
    (averageMap s e (TestFunction.postcompCLM Complex.ofRealCLM (TestFunction.monoCLM ℝ f))).val 1 = _
  unfold additiveJacquetIntegral
  apply integral_congr_ae
  filter_upwards with u
  simp only [additiveJacquetKernel, mul_one, averageMap_apply, borelAverage,
    jacquetOrbitKernel, integral_mul_const, jacquetOrbit_val, Units.val_mul]
  have hcoe : ((TestFunction.monoCLM ℝ f : 𝓓(invertibleDomain r, ℝ)) : M → ℝ) = f := by
    simp [longestCell_le]
  simp only [TestFunction.postcompCLM_apply, hcoe, mul_assoc]
  rfl

private theorem inverseWeight_eq_inv_diagChar (s : P) (e : Signs) (b : B) :
    inverseWeight (positionBorelCharacter s e) b = (diagChar s e b.val.val)⁻¹ := rfl

private theorem charFun_eq_sign_mul_exp (e : Fin 2) (s : ℂ) {x : ℝ} (hx : x ≠ 0) :
    charFun e s x = ((x / |x| : ℝ) : ℂ) ^ e.val * Complex.exp ((Real.log |x| : ℂ) * s) := by
  rw [RealJacquetFrobenius.charFun, Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (abs_ne_zero.mpr hx)),
    ← Complex.ofReal_log (abs_nonneg _)]

private def diagonalSign (e : Signs) (b : B) : ℂ :=
  ∏ i : Fin (r + 1), ((b.val.val i i / |b.val.val i i| : ℝ) : ℂ) ^ (e i).val

private theorem diagChar_eq_diagonalSign_mul_exp (s : P) (e : Signs) (b : B) :
    diagChar s e b.val.val = diagonalSign e b *
      Complex.exp (∑ i : Fin (r + 1), (Real.log |b.val.val i i| : ℂ) * s i) := by
  rw [diagonalSign, Complex.exp_sum, ← Finset.prod_mul_distrib, diagChar]
  exact Finset.prod_congr rfl fun i _ => charFun_eq_sign_mul_exp _ _ (diag_ne_zero b.property b.val.isUnit i)

private theorem differentiable_inverseWeight (e : Signs) (b : B) :
    Differentiable ℂ (fun s : P => inverseWeight (positionBorelCharacter s e) b) := by
  simp_rw [inverseWeight_eq_inv_diagChar]
  apply Differentiable.inv
  · simp_rw [diagChar_eq_diagonalSign_mul_exp]
    exact ((Differentiable.fun_sum fun i _ =>
      (ContinuousLinearMap.proj i : P →L[ℂ] ℂ).differentiable.const_mul _).cexp).const_mul _
  · intro s
    exact Finset.prod_ne_zero_iff.mpr fun i _ => charFun_ne_zero _ _ (diag_ne_zero b.property b.val.isUnit i)

private theorem continuous_inverseWeight_family (e : Signs) :
    Continuous (fun q : P × B => inverseWeight (positionBorelCharacter q.1 e) q.2) := by
  simp_rw [inverseWeight_eq_inv_diagChar]
  apply Continuous.inv₀
  · simp_rw [diagChar_eq_diagonalSign_mul_exp]
    have hEntry (i : Fin (r + 1)) : Continuous (fun q : P × B => q.2.val.val i i) :=
      ((Units.continuous_val.comp continuous_subtype_val).matrix_elem i i).comp continuous_snd
    have hn (i : Fin (r + 1)) (q : P × B) : |q.2.val.val i i| ≠ 0 :=
      abs_ne_zero.mpr (diag_ne_zero q.2.property q.2.val.isUnit i)
    have hSign : Continuous (fun q : P × B => diagonalSign e q.2) :=
      continuous_finsetProd _ fun i _ => (Complex.continuous_ofReal.comp ((hEntry i).div (hEntry i).abs (hn i))).pow _
    have hExp : Continuous (fun q : P × B =>
        Complex.exp (∑ i : Fin (r + 1), (Real.log |q.2.val.val i i| : ℂ) * q.1 i)) :=
      (continuous_finsetSum _ fun i _ => (Complex.continuous_ofReal.comp ((hEntry i).abs.log (hn i))).mul
        ((continuous_apply i).comp continuous_fst)).cexp
    exact hSign.mul hExp
  · intro q
    exact Finset.prod_ne_zero_iff.mpr fun i _ => charFun_ne_zero _ _ (diag_ne_zero q.2.property q.2.val.isUnit i)

/-- The reversal-cell integral of each compact test is entire in the inducing exponents. -/
theorem differentiable_reversalIntegral (a : ℝˣ) (e : Signs) (f : 𝓓(O, ℝ)) :
    Differentiable ℂ (fun s : P => ∫ p : H, jacquetOrbitKernel a s e f p ∂((upperStepHaar r a).prod dx)) := by
  let : (upperStepHaar r a).IsHaarMeasure := upperStepHaar_isHaar r a
  let : SigmaFinite (upperStepHaar r a) := upperStepHaar_sigmaFinite r a
  let μ := (upperStepHaar r a).prod dx
  let V := (fun p : H => (jacquetOrbit r p).val) ⁻¹' tsupport f
  have hV : IsCompact V := isCompact_jacquetOrbit_preimage f.hasCompactSupport f.tsupport_subset
  let : IsFiniteMeasure (μ.restrict V) := isFiniteMeasure_restrict.mpr hV.measure_lt_top.ne
  let F (s : P) (p : H) := jacquetOrbitKernel a s e f p
  have hZero (s : P) (p : H) (hp : p ∉ V) : F s p = 0 := by
    simp only [F, jacquetOrbitKernel, image_eq_zero_of_notMem_tsupport hp, Complex.ofReal_zero, mul_zero, zero_mul]
  have hF (p : H) : Differentiable ℂ (fun s : P => F s p) :=
    ((differentiable_inverseWeight e p.2).mul_const _).mul_const _
  have hJoint : Continuous (fun q : P × H => F q.1 q.2) :=
    (((continuous_inverseWeight_family e).comp (continuous_fst.prodMk (continuous_snd.comp continuous_snd))).mul
      (Complex.continuous_ofReal.comp (f.contDiff.continuous.comp
        (continuous_subtype_val.comp ((jacquetOrbit r).continuous.comp continuous_snd))))).mul
      ((continuous_phase a).comp (continuous_fst.comp continuous_snd))
  have hInt : DifferentiableOn ℂ (fun s => ∫ p in V, F s p ∂μ) univ := by
    apply Langlands.Analysis.SeveralComplex.differentiableOn_integral_of_bounded (μ.restrict V) F isOpen_univ
      (fun p => (hF p).differentiableOn)
    · intro s _
      exact (continuous_jacquetOrbitKernel a s e f.contDiff.continuous).aestronglyMeasurable
    · intro C _ hC
      obtain ⟨A, hA⟩ := (hC.prod hV).exists_bound_of_continuousOn hJoint.continuousOn
      refine ⟨max A 0, fun s hs p => ?_⟩
      by_cases hp : p ∈ V
      · exact (hA (s, p) ⟨hs, hp⟩).trans (le_max_left _ _)
      · rw [hZero s p hp, norm_zero]
        exact le_max_right _ _
  have he (s : P) : (∫ p in V, F s p ∂μ) = ∫ p : H, jacquetOrbitKernel a s e f p ∂μ :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (hZero s)
  simpa only [he, differentiableOn_univ] using hInt

/-- The strict-chamber Jacquet distribution is a covariant order-zero seed whose
reversal-cell evaluations extend to entire integrals. -/
def RealJacquetTestDistributionStatement : Prop :=
  ∀ (a : ℝˣ) (e : Signs),
    (∀ f : 𝓓(O, ℝ), Differentiable ℂ (fun s : P =>
      ∫ p : H, jacquetOrbitKernel a s e f p ∂((upperStepHaar r a).prod dx))) ∧
    ∀ (s : P) (hDom : IsStrictlyDominant (realPositionExponent (normalizedCharacterBlocks s e)) r),
      IsUnipotentWhittakerCovariant (dominantDistribution a s e hDom) (-a) ∧
      (∀ (K : Compacts M) (hK : (K : Set M) ⊆ invertibleDomain r),
        ∃ C : ℝ, 0 ≤ C ∧ ∀ f, ‖dominantDistribution a s e hDom (TestFunction.ofSupportedIn hK f)‖ ≤
          C * p₀(K) f) ∧
      ∀ f : 𝓓(O, ℝ), dominantDistribution a s e hDom (TestFunction.monoCLM ℝ f) =
        ∫ p : H, jacquetOrbitKernel a s e f p ∂((upperStepHaar r a).prod dx)

theorem realJacquetTestDistribution : RealJacquetTestDistributionStatement (r := r) := by
  intro a e
  refine ⟨differentiable_reversalIntegral a e, fun s hDom => ?_⟩
  exact ⟨dominantDistribution_covariant a s e hDom, dominantDistribution_order_zero a s e hDom,
    dominantDistribution_reversalIntegral a s e hDom⟩

end Langlands.Global.RankinSelbergGlobal.RealJacquetTestDistribution
