import Langlands.Representation.RankinSelberg.RankOneExtensionSpanComparisonCore
import Langlands.Representation.RankinSelberg.RankOneExtensionWhittakerCells
import Langlands.Representation.RankinSelberg.RankOneExtensionDisintegration
import Langlands.Representation.RankinSelberg.RankOneExtensionLowerJacquetFunctionalStatement
import Langlands.Representation.RankinSelberg.RankOneExtensionCompactSectionProof
import Langlands.Representation.RankinSelberg.RankOneExtensionScalarCutoffProof
import Langlands.Representation.RankinSelberg.UnequalRankBlockZeroContinuedFormsProof
import Langlands.Representation.RankinSelberg.CentralSpectralElement
import Langlands.HarmonicAnalysis.PadicScalarHaarScalingProof
import Langlands.LocalField.Normalization.Proof
import Langlands.LocalField.Uniformizer
import Langlands.Group.GL.NormalizedCharacter
import Langlands.Representation.MatrixCoefficient.LawsProof
import Langlands.Representation.Induction.CompactQuotientProof
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Assembly of the rank-one extension span comparison

JPSS (1983), Lemma (5.5), printed pp. 423–427. For a Whittaker function `W₀` of `π` and an
inverse Whittaker function `W'` of `σ₁`, the scalar cutoff of `W₀`, a compact section `f` of the
lower induction `I(σ₁, χ)` and the lower Jacquet functional `Λ` give a Whittaker function `W₁`
of `π` and the inverse Whittaker function `W''(g) = Λ(I(g) f)` with
`Ψ_ind(s; W₁, W'') = C ρ(U) Ψ_base(s; W₀, W')`. The change of variables is
`rankOneExtensionUnfoldingCore`; this module verifies its hypotheses for
`H(z) = W₁(ι z) c_f(z) |det z|^(s - (k+1)/2)`.

The disintegration of the quotient measure and the Jacquet functional enter as the hypotheses
`LowerBlockQuotientDisintegrationStatement` and `RankOneExtensionLowerJacquetFunctionalStatement`.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration Matrix
open scoped ENNReal NNReal

universe uF uV uW

section Integrand

variable {K : Type uF} [Field K] [TopologicalSpace K] (ψ : UnitaryAdditiveCharacter K)
  (abv : AbsoluteValue K ℝ) {t k : ℕ}

omit [TopologicalSpace K] in
theorem determinantWeight_mul_of_det_eq_one {m : ℕ} {g : Langlands.GeneralLinear m K}
    (hg : g.val.det = 1) (h : Langlands.GeneralLinear m K) (s : ℂ) :
    determinantWeight abv (g * h) s = determinantWeight abv h s := by
  simp [determinantWeight, Matrix.det_mul, hg]

/-- The function `H(z) = W(ι z) c(z) |det z|^s` on `GL(1 + (t + 1))`. -/
def rankOneExtensionUnfoldingFunction (W : WhittakerFunctions ψ ((1 + (t + 1)) + k))
    (c : Langlands.GeneralLinear (1 + (t + 1)) K → ℂ) (s : ℂ)
    (z : Langlands.GeneralLinear (1 + (t + 1)) K) : ℂ :=
  W.val (rankInclusion (k + 1) z) * c z * determinantWeight abv z s

/-- `H(B(n, 0, 1) z) = H(z)` for `n ∈ N_(t+1)` when `c` transforms by the inverse character. -/
theorem rankOneExtensionUnfoldingFunction_lowerBlock_mul
    (W : WhittakerFunctions ψ ((1 + (t + 1)) + k))
    (c : Langlands.GeneralLinear (1 + (t + 1)) K → ℂ)
    (hc : ∀ (n : upperUnipotent (t + 1) K) (z : Langlands.GeneralLinear (1 + (t + 1)) K),
      c (rankOneExtensionLowerBlock t n.val 0 1 * z) =
        ((inverseStandardCharacter ψ t n : ℂˣ) : ℂ) * c z)
    (s : ℂ) (n : upperUnipotent (t + 1) K) (z : Langlands.GeneralLinear (1 + (t + 1)) K) :
    rankOneExtensionUnfoldingFunction ψ abv W c s (rankOneExtensionLowerBlock t n.val 0 1 * z) =
      rankOneExtensionUnfoldingFunction ψ abv W c s z := by
  have hdet : (rankOneExtensionLowerBlock t n.val 0 1).val.det = 1 := by
    rw [det_rankOneExtensionLowerBlock, unipotent_det]
    simp
  simp only [rankOneExtensionUnfoldingFunction]
  rw [whittaker_rankInclusion_lowerBlock_mul, hc, determinantWeight_mul_of_det_eq_one abv hdet]
  have hθ : (standardCharacter ψ t n : ℂ) * ((inverseStandardCharacter ψ t n : ℂˣ) : ℂ) = 1 := by
    rw [inverseStandardCharacter, MonoidHom.inv_apply, ← Units.val_mul, mul_inv_cancel,
      Units.val_one]
  calc (standardCharacter ψ t n : ℂ) * W.val (rankInclusion (k + 1) z) *
        (((inverseStandardCharacter ψ t n : ℂˣ) : ℂ) * c z) * determinantWeight abv z s
      = ((standardCharacter ψ t n : ℂ) * ((inverseStandardCharacter ψ t n : ℂˣ) : ℂ)) *
          (W.val (rankInclusion (k + 1) z) * c z * determinantWeight abv z s) := by ring
    _ = _ := by rw [hθ, one_mul]

/-- `H(u(y) z) = (W(ι z) |det z|^s) · c(u(y) z) ψ(y_t)`. -/
theorem rankOneExtensionUnfoldingFunction_upperCell_mul
    (W : WhittakerFunctions ψ ((1 + (t + 1)) + k))
    (c : Langlands.GeneralLinear (1 + (t + 1)) K → ℂ) (s : ℂ) (y : Fin (t + 1) → K)
    (z : Langlands.GeneralLinear (1 + (t + 1)) K) :
    rankOneExtensionUnfoldingFunction ψ abv W c s (rankOneExtensionUpperCell t y * z) =
      (W.val (rankInclusion (k + 1) z) * determinantWeight abv z s) *
        (c (rankOneExtensionUpperCell t y * z) * ψ.complex (y (Fin.last t))) := by
  simp only [rankOneExtensionUnfoldingFunction]
  rw [whittaker_rankInclusion_upperCell_mul,
    determinantWeight_mul_of_det_eq_one abv (det_rankOneExtensionUpperCell y)]
  ring

end Integrand

section Jacquet

variable {Y : Type*} [MeasurableSpace Y]

/-- If `V = ∫ S` whenever `S` is integrable, then `A V = ∫ A S` whenever `A S` is integrable. -/
theorem mul_eq_integral_of_integrable_mul (μ : Measure Y) (A V : ℂ) (S : Y → ℂ)
    (hV : Integrable S μ → V = ∫ y, S y ∂μ) (hAS : Integrable (fun y => A * S y) μ) :
    A * V = ∫ y, A * S y ∂μ := by
  by_cases hA : A = 0
  · simp [hA]
  · have hS : Integrable S μ := by
      have h := hAS.const_mul A⁻¹
      simpa only [← mul_assoc, inv_mul_cancel₀ hA, one_mul] using h
    rw [hV hS, integral_const_mul]

end Jacquet

section Measures

variable {K : Type*} [Field K] [TopologicalSpace K] [IsTopologicalRing K] [T2Space K]
  [MeasurableSpace K] [BorelSpace K]

/-- An additive Haar measure scaled by a factor `≠ 1` under some dilation has no atoms. -/
theorem nullSingletonClass_of_map_mul (ν : Measure K) [ν.IsAddLeftInvariant]
    [IsFiniteMeasureOnCompacts ν] (χ : K →*₀ ℝ≥0) (a : K) (ha : a ≠ 0) (hχa : χ a ≠ 1)
    (hmap : ν.map (fun x => a * x) = (χ a)⁻¹ • ν) : NullSingletonClass ν := by
  have h0 : ν {0} = 0 := by
    have hm : Measurable fun x : K => a * x := (continuous_const.mul continuous_id).measurable
    have hpre : (fun x : K => a * x) ⁻¹' {0} = {0} := by
      ext x
      simp [ha]
    have h := congrArg (fun m : Measure K => m {0}) hmap
    simp only [Measure.map_apply hm (measurableSet_singleton 0), hpre, Measure.smul_apply,
      ENNReal.smul_def, smul_eq_mul] at h
    have htop : ν {0} ≠ ∞ := (isCompact_singleton.measure_lt_top).ne
    by_contra hne
    have h1 : (((χ a)⁻¹ : ℝ≥0) : ℝ≥0∞) = 1 := by
      have h' : 1 * ν {0} = (((χ a)⁻¹ : ℝ≥0) : ℝ≥0∞) * ν {0} := by rw [one_mul]; exact h
      exact ((ENNReal.mul_left_inj hne htop).mp h').symm
    exact hχa (inv_eq_one.mp (ENNReal.coe_eq_one.mp h1))
  refine ⟨fun x => ?_⟩
  have hpre : (fun y : K => -x + y) ⁻¹' {0} = {x} := by
    ext y
    simp [eq_comm]
  rw [← hpre, measure_preimage_add, h0]

end Measures

section ScalarLower

variable {K : Type*} [Field K] [TopologicalSpace K]

theorem continuous_rankOneExtensionScalarLower :
    Continuous (rankOneExtensionScalarLower : Kˣ → lowerTriangularSubgroup 1 K) := by
  have hinv : ∀ a : Kˣ,
      ((rankOneExtensionScalarLower a : Langlands.GeneralLinear 1 K))⁻¹ =
        (rankOneExtensionScalarLower a⁻¹ : Langlands.GeneralLinear 1 K) := by
    intro a
    refine inv_eq_of_mul_eq_one_right ?_
    apply Units.ext
    ext i j
    rw [Subsingleton.elim i 0, Subsingleton.elim j 0]
    simp [Matrix.mul_apply]
  refine continuous_induced_rng.2 (Units.continuous_iff.mpr ⟨?_, ?_⟩)
  · refine continuous_matrix fun i j => ?_
    simp only [Function.comp_apply, rankOneExtensionScalarLower_apply]
    exact Units.continuous_val
  · refine continuous_matrix fun i j => ?_
    simp only [Function.comp_apply, hinv, rankOneExtensionScalarLower_apply]
    exact Units.continuous_coe_inv

omit [TopologicalSpace K] in
@[simp] theorem lowerScalarEntry_one : lowerScalarEntry (1 : lowerTriangularSubgroup 1 K) = 1 := by
  simp [lowerScalarEntry]

/-- The preimage of a compact set `U ∌ 0` under the scalar entry is compact. -/
theorem isCompact_preimage_lowerScalarEntry [IsTopologicalDivisionRing K] {U : Set K}
    (hU : IsCompact U) (h0 : (0 : K) ∉ U) :
    IsCompact (lowerScalarEntry ⁻¹' U : Set (lowerTriangularSubgroup 1 K)) := by
  have hc : IsCompact ((Units.val : Kˣ → K) ⁻¹' U) :=
    Units.isEmbedding_val₀.isInducing.isCompact_preimage' hU fun x hx =>
      ⟨Units.mk0 x fun h => h0 (h ▸ hx), rfl⟩
  have heq : (lowerScalarEntry ⁻¹' U : Set (lowerTriangularSubgroup 1 K)) =
      rankOneExtensionScalarLower '' ((Units.val : Kˣ → K) ⁻¹' U) := by
    ext h
    constructor
    · intro hh
      refine ⟨lowerScalarUnit h, hh, ?_⟩
      apply Subtype.ext
      apply Units.ext
      ext i j
      rw [Subsingleton.elim i 0, Subsingleton.elim j 0, rankOneExtensionScalarLower_apply]
      rfl
    · rintro ⟨a, ha, rfl⟩
      simpa [Set.mem_preimage] using ha
  rw [heq]
  exact hc.image continuous_rankOneExtensionScalarLower

end ScalarLower

section Weights

variable {K : Type*} [Field K] {t : ℕ}

theorem determinantWeight_lowerBlock_mul_upperCell (abv : AbsoluteValue K ℝ)
    (m : Langlands.GeneralLinear (t + 1) K) (x : Fin (t + 1) → K) (a : Kˣ)
    (ha : abv (a : K) = 1) (y : Fin (t + 1) → K) (s : ℂ) :
    determinantWeight abv (rankOneExtensionLowerBlock t m x a * rankOneExtensionUpperCell t y) s =
      determinantWeight abv m s := by
  simp only [determinantWeight, Units.val_mul, Matrix.det_mul, det_rankOneExtensionLowerBlock,
    det_rankOneExtensionUpperCell, mul_one, map_mul, ha]

theorem sqrt_inv_mul_cpow {D : ℝ} (hD : 0 < D) (z : ℂ) :
    ((Real.sqrt D : ℝ) : ℂ)⁻¹ * (D : ℂ) ^ z = (D : ℂ) ^ (z - 1 / 2) := by
  have hD0 : (D : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hD.ne'
  rw [Complex.cpow_sub _ _ hD0, Real.sqrt_eq_rpow, Complex.ofReal_cpow hD.le]
  push_cast
  exact (div_eq_inv_mul _ _).symm

end Weights

section Smooth

/-- For a smooth representation, `g ↦ Λ(ρ(g) v)` is continuous for every functional `Λ`. -/
theorem continuous_dual_apply_of_isSmooth {G X : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [AddCommGroup X] [Module ℂ X] {ρ : Representation ℂ G X}
    (hρ : IsSmooth ρ) (Λ : Module.Dual ℂ X) (v : X) : Continuous fun g => Λ (ρ g v) :=
  (matrixCoefficient_isLocallyConstant ρ Λ v (hρ v)).continuous

end Smooth

section Padic

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
  {V : Type uV} [AddCommGroup V] [Module ℂ V] {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {t k : ℕ}

/-- JPSS (1983), Lemma (5.5), printed 425–426: on the cell `B(m, x, a) u(y)`, the function
`H(z) = W₁(ι z) c_f(z) |det z|^(s - (k+1)/2)` is `1_U(a) · W₀(B(m, x, 1)) W'(m)
|det m|^(s - (k+2)/2) · φ(y)`. -/
theorem rankOneExtensionUnfoldingFunction_lowerBlock_mul_upperCell
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (χ : letI := F.canonicalTopologicalData.topology; Quasicharacter F.Carrier)
    (π : Representation ℂ (Langlands.GeneralLinear ((1 + (t + 1)) + k + 1) F.Carrier) V)
    (ℓπ : letI := F.canonicalTopologicalData.topology; glFunctionals ψ ((1 + (t + 1)) + k) π)
    (f₁ f₂ : (coefficientModel π ℓπ).toSubmodule) (v₁ : V) (hv₁ : modelMap π ℓπ v₁ = f₁)
    (U : Set F.Carrier)
    (hU : ∀ y ∈ U, normalizedAbsoluteValue F.canonicalTopologicalData y = 1)
    (hin : ∀ (m : Langlands.GeneralLinear (t + 1) F.Carrier) (x : Fin (t + 1) → F.Carrier)
      (a : F.Carrierˣ), (a : F.Carrier) ∈ U →
        f₁.val.val (rankOneExtensionEmbeddedLowerBlock t k m x a) =
          ((χ a : ℂˣ) : ℂ)⁻¹ * f₂.val.val (rankOneExtensionEmbeddedLowerBlock t k m x 1))
    (hout : ∀ (m : Langlands.GeneralLinear (t + 1) F.Carrier) (x : Fin (t + 1) → F.Carrier)
      (a : F.Carrierˣ), (a : F.Carrier) ∉ U →
        f₁.val.val (rankOneExtensionEmbeddedLowerBlock t k m x a) = 0)
    (σ : Representation ℂ (Langlands.GeneralLinear (t + 1) F.Carrier) W)
    (ℓ : letI := F.canonicalTopologicalData.topology; Whittaker.glInverseFunctionals ψ t σ)
    (w : W) (sec : rankOneExtensionLowerSection F t χ σ) (φ : (Fin (t + 1) → F.Carrier) → ℂ)
    (hsec : ∀ y, rankOneExtensionLowerSectionEval F t χ σ sec (rankOneExtensionUpperCell t y) =
      φ y • rankOneExtensionLowerPureTensor w (ULift.up 1))
    (hfix : ∀ y ∈ Function.support φ,
      π (rankInclusion (k + 1) (rankOneExtensionUpperCell t y)) v₁ = v₁)
    (s : ℂ) (m : Langlands.GeneralLinear (t + 1) F.Carrier) (x : Fin (t + 1) → F.Carrier)
    (a : F.Carrierˣ) (y : Fin (t + 1) → F.Carrier) :
    letI := F.canonicalTopologicalData.topology
    rankOneExtensionUnfoldingFunction ψ (normalizedAbsoluteValue F.canonicalTopologicalData)
        f₁.val (rankOneExtensionLowerSectionCoefficient F t χ σ ψ ℓ sec)
        (s - ((0 + k + 1 : ℕ) : ℂ) / 2)
        (rankOneExtensionLowerBlock t m x a * rankOneExtensionUpperCell t y) =
      U.indicator (fun _ => (1 : ℂ)) (a : F.Carrier) *
        (f₂.val.val (rankOneExtensionEmbeddedLowerBlock t k m x 1) * ℓ.val (σ m w) *
          determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData) m
            (s - ((1 + k + 1 : ℕ) : ℂ) / 2)) * φ y := by
  let T := F.canonicalTopologicalData
  let := T.topology
  have hW₁ : ∀ g, f₁.val.val g = ℓπ.val (π g v₁) := by
    intro g
    rw [← hv₁]
    rfl
  have hcoef : rankOneExtensionLowerSectionCoefficient F t χ σ ψ ℓ sec
      (rankOneExtensionLowerBlock t m x a * rankOneExtensionUpperCell t y) =
        (((NNReal.sqrt ((T.determinantNorm (t + 1) m / T.normalizedAbsUnits a ^ (t + 1) :
          ℝ≥0ˣ) : ℝ≥0) : ℝ) : ℂ))⁻¹ * ((χ a : ℂˣ) : ℂ) * (φ y * ℓ.val (σ m w)) := by
    rw [rankOneExtensionLowerSectionCoefficient_lowerBlock_mul, hsec, map_smul,
      rankOneExtensionTensorContraction_pure, smul_eq_mul]
    simp [T]
  simp only [rankOneExtensionUnfoldingFunction]
  rw [hcoef]
  by_cases hφ : φ y = 0
  · simp [hφ]
  have hfixy := hfix y hφ
  rw [map_mul, hW₁, map_mul, Module.End.mul_apply, hfixy, ← hW₁]
  change f₁.val.val (rankOneExtensionEmbeddedLowerBlock t k m x a) * _ * _ = _
  by_cases ha : (a : F.Carrier) ∈ U
  · have ha1 : normalizedAbsoluteValue T (a : F.Carrier) = 1 := hU _ ha
    have hunit : T.normalizedAbsUnits a = 1 :=
      Units.ext (NNReal.eq (by simpa using ha1))
    have hpos : 0 < T.normalizedAbs (Matrix.det m.val) := by
      rcases (T.normalizedAbs_nonneg (Matrix.det m.val)).lt_or_eq with h | h
      · exact h
      · exact absurd ((T.normalizedAbs_eq_zero_iff _).mp h.symm)
          (Matrix.GeneralLinearGroup.det_ne_zero m)
    have hdw : (((NNReal.sqrt (T.determinantNorm (t + 1) m : ℝ≥0) : ℝ) : ℂ))⁻¹ *
        determinantWeight (normalizedAbsoluteValue T) m (s - ((0 + k + 1 : ℕ) : ℂ) / 2) =
        determinantWeight (normalizedAbsoluteValue T) m (s - ((1 + k + 1 : ℕ) : ℂ) / 2) := by
      rw [determinantWeight, determinantWeight, Real.coe_sqrt]
      change ((Real.sqrt (T.normalizedAbs (Matrix.det m.val)) : ℝ) : ℂ)⁻¹ *
          ((T.normalizedAbs (Matrix.det m.val) : ℝ) : ℂ) ^ _ = _
      rw [sqrt_inv_mul_cpow hpos]
      congr 1
      push_cast
      ring
    rw [hin m x a ha, hunit, one_pow, div_one,
      determinantWeight_lowerBlock_mul_upperCell _ m x a ha1, Set.indicator_of_mem ha, ← hdw]
    have hχ : ((χ a : ℂˣ) : ℂ)⁻¹ * ((χ a : ℂˣ) : ℂ) = 1 := inv_mul_cancel₀ (Units.ne_zero _)
    linear_combination (f₂.val.val (rankOneExtensionEmbeddedLowerBlock t k m x 1) *
      (((NNReal.sqrt (T.determinantNorm (t + 1) m : ℝ≥0) : ℝ) : ℂ))⁻¹ * (φ y * ℓ.val (σ m w)) *
        determinantWeight (normalizedAbsoluteValue T) m (s - ((0 + k + 1 : ℕ) : ℂ) / 2)) * hχ
  · rw [hout m x a ha]
    simp [ha]

/-- The function `H(z) = W(ι z) c(z) |det z|^s` is continuous for smooth `π` and
continuous `c`. -/
theorem continuous_rankOneExtensionUnfoldingFunction_of_continuous
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (π : Representation ℂ (Langlands.GeneralLinear ((1 + (t + 1)) + k + 1) F.Carrier) V)
    (hπ : letI := F.canonicalTopologicalData.topology; IsSmooth π)
    (ℓπ : letI := F.canonicalTopologicalData.topology; glFunctionals ψ ((1 + (t + 1)) + k) π)
    (f₁ : (coefficientModel π ℓπ).toSubmodule)
    (c : Langlands.GeneralLinear (1 + (t + 1)) F.Carrier → ℂ)
    (hc : letI := F.canonicalTopologicalData.topology; Continuous c) (s : ℂ) :
    letI := F.canonicalTopologicalData.topology
    Continuous (rankOneExtensionUnfoldingFunction ψ
      (normalizedAbsoluteValue F.canonicalTopologicalData) f₁.val c s) := by
  let T := F.canonicalTopologicalData
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  have : IsTopologicalRing F.Carrier := inferInstance
  obtain ⟨v, rfl⟩ := modelMap_surjective π ℓπ f₁
  have hW : Continuous fun g => (modelMap π ℓπ v).val.val g :=
    (matrixCoefficient_isLocallyConstant π ℓπ.val v (hπ v)).continuous
  have hι : Continuous (rankInclusion (k + 1) :
      Langlands.GeneralLinear (1 + (t + 1)) F.Carrier → _) :=
    (rankInclusionContinuous (k + 1)).continuous
  have hdet : Continuous fun g : Langlands.GeneralLinear (1 + (t + 1)) F.Carrier =>
      normalizedAbsoluteValue T (Matrix.det g.val) :=
    (NNReal.continuous_coe.comp T.continuous_normalizedAbsHom).comp
      Units.continuous_val.matrix_det
  have hweight : Continuous fun g : Langlands.GeneralLinear (1 + (t + 1)) F.Carrier =>
      determinantWeight (normalizedAbsoluteValue T) g s := by
    apply (Complex.continuous_ofReal.comp hdet).cpow continuous_const
    intro g
    exact Complex.ofReal_mem_slitPlane.mpr ((normalizedAbsoluteValue T).pos g.det_ne_zero)
  exact ((hW.comp hι).mul hc).mul hweight

/-- The function `H` with the scalar coefficient `c_f` of a lower section is continuous. -/
theorem continuous_rankOneExtensionUnfoldingFunction
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (χ : letI := F.canonicalTopologicalData.topology; Quasicharacter F.Carrier)
    (π : Representation ℂ (Langlands.GeneralLinear ((1 + (t + 1)) + k + 1) F.Carrier) V)
    (hπ : letI := F.canonicalTopologicalData.topology; IsSmooth π)
    (ℓπ : letI := F.canonicalTopologicalData.topology; glFunctionals ψ ((1 + (t + 1)) + k) π)
    (f₁ : (coefficientModel π ℓπ).toSubmodule)
    (σ : Representation ℂ (Langlands.GeneralLinear (t + 1) F.Carrier) W)
    (ℓ : letI := F.canonicalTopologicalData.topology; Whittaker.glInverseFunctionals ψ t σ)
    (sec : rankOneExtensionLowerSection F t χ σ) (s : ℂ) :
    letI := F.canonicalTopologicalData.topology
    Continuous (rankOneExtensionUnfoldingFunction ψ
      (normalizedAbsoluteValue F.canonicalTopologicalData) f₁.val
      (rankOneExtensionLowerSectionCoefficient F t χ σ ψ ℓ sec) s) := by
  let T := F.canonicalTopologicalData
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  exact continuous_rankOneExtensionUnfoldingFunction_of_continuous F ψ π hπ ℓπ f₁ _
    ((Induction.eval_isLocallyConstant _ _ sec).comp
      (rankOneExtensionWhittakerContraction F t σ ψ ℓ)).continuous s

/-- The inverse Whittaker function `g ↦ Λ(I(g) f)` of a lower section `f` is continuous. -/
theorem continuous_rankOneExtensionLowerCoefficient
    (χ : letI := F.canonicalTopologicalData.topology; Quasicharacter F.Carrier)
    (σ : Representation ℂ (Langlands.GeneralLinear (t + 1) F.Carrier) W)
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (Λ : letI := F.canonicalTopologicalData.topology
      letI := F.canonicalTopologicalData.valuativeRel
      letI := F.canonicalTopologicalData.localField
      Whittaker.glInverseFunctionals ψ (1 + t) (rankOneExtensionLowerModel F t χ σ))
    (sec : rankOneExtensionLowerSection F t χ σ) :
    letI := F.canonicalTopologicalData.topology
    Continuous fun g : Langlands.GeneralLinear (1 + (t + 1)) F.Carrier =>
      Λ.val (rankOneExtensionLowerModel F t χ σ g
        ((rankOneExtensionLowerModel F t χ σ).asModuleEquiv sec)) := by
  let T := F.canonicalTopologicalData
  let := T.topology
  let := T.generalLinearTopologicalGroup (1 + (t + 1))
  exact continuous_dual_apply_of_isSmooth (T.isSmooth_normalizedOppositeParabolicInduced _ _)
    Λ.val _

end Padic

section ZeroRows

/-- Integration against a point mass on a subsingleton space is evaluation. -/
theorem integral_dirac_of_subsingleton {X : Type*} [MeasurableSpace X] [Subsingleton X]
    (f : X → ℂ) (a : X) : ∫ x, f x ∂(Measure.dirac a) = f a := by
  have hf : f = fun _ => f a := funext fun x => by rw [Subsingleton.elim x a]
  rw [hf, integral_const]
  simp

end ZeroRows

section Pointwise

/-- JPSS (1983), Lemma (5.5), printed pp. 423–427, pointwise form. Let `W₀` be a Whittaker
function of `π` and `W'` an inverse Whittaker function of `σ₁` whose block-one integral
`Ψ_base(s; W₀, W')` converges absolutely on a right half-plane. Then there are a Whittaker
function `W₁` of `π` (the scalar cutoff of `W₀`), an inverse Whittaker function `W''` of the
lower induction (`W''(g) = Λ(I(g) f)` for a compact section `f` and the Jacquet functional `Λ`),
and a constant `c = C ρ(U) ≠ 0` with `Ψ_ind(s; W₁, W'') = c Ψ_base(s; W₀, W')` and absolute
convergence of the block-zero integral on the same half-plane. The disintegration of the
quotient measure and the Jacquet functional are the hypotheses `hdis` and `hJ`. -/
theorem rankOneExtensionSpanComparison_pointwise
    (hdis : LowerBlockQuotientDisintegrationStatement.{uF})
    (hJ : RankOneExtensionLowerJacquetFunctionalStatement.{uF, uW})
    (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
    (r t k : ℕ)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
    (σ₁ : Representation ℂ (Langlands.GeneralLinear (t + 1) F.Carrier) W)
    (χ : letI := F.canonicalTopologicalData.topology; Quasicharacter F.Carrier)
    (hrB : r = t + (1 + k + 1)) (hrI : r = (1 + t) + (0 + k + 1))
    (hπ : letI := F.canonicalTopologicalData.topology; IsSmooth π)
    (hσ : letI := F.canonicalTopologicalData.topology; IsSmooth σ₁) :
    let χlift : Representation ℂ (Langlands.GeneralLinear 1 F.Carrier)
        (ULift.{uW} ℂ) :=
      (ULift.moduleEquiv.symm.conjRingEquiv.toMonoidHom).comp
        (rankOneCharacter (χ : F.Carrierˣ →* ℂˣ))
    letI := F.canonicalTopologicalData.topology
    letI := F.canonicalTopologicalData.valuativeRel
    letI := F.canonicalTopologicalData.localField
    letI := borel F.Carrier
    letI : BorelSpace F.Carrier := ⟨rfl⟩
    letI := borel (Langlands.GeneralLinear (t + 1) F.Carrier)
    letI : BorelSpace (Langlands.GeneralLinear (t + 1) F.Carrier) := ⟨rfl⟩
    letI := borel (upperUnipotent (t + 1) F.Carrier)
    letI : BorelSpace (upperUnipotent (t + 1) F.Carrier) := ⟨rfl⟩
    letI := borel (LeftUnipotentQuotient t F.Carrier)
    letI : BorelSpace (LeftUnipotentQuotient t F.Carrier) := ⟨rfl⟩
    letI := borel (Langlands.GeneralLinear ((1 + t) + 1) F.Carrier)
    letI : BorelSpace (Langlands.GeneralLinear ((1 + t) + 1) F.Carrier) := ⟨rfl⟩
    letI := borel (upperUnipotent ((1 + t) + 1) F.Carrier)
    letI : BorelSpace (upperUnipotent ((1 + t) + 1) F.Carrier) := ⟨rfl⟩
    letI := borel (LeftUnipotentQuotient (1 + t) F.Carrier)
    letI : BorelSpace (LeftUnipotentQuotient (1 + t) F.Carrier) := ⟨rfl⟩
    ∀ [Measure.IsMulRightInvariant (unipotentHaar F.Carrier t)]
      [Measure.IsMulRightInvariant (unipotentHaar F.Carrier (1 + t))]
      (μbase : Measure (LeftUnipotentQuotient t F.Carrier))
      (μind : Measure (LeftUnipotentQuotient (1 + t) F.Carrier)),
      IsCompatible (upperUnipotent (t + 1) F.Carrier)
        (generalLinearHaar F.Carrier t) (unipotentHaar F.Carrier t) μbase →
      IsCompatible (upperUnipotent ((1 + t) + 1) F.Carrier)
        (generalLinearHaar F.Carrier (1 + t)) (unipotentHaar F.Carrier (1 + t)) μind →
      ∀ W₀ ∈ whittakerSet ψ r π, ∀ W' ∈ inverseWhittakerSet ψ t σ₁,
        (∃ a : ℝ, ∀ s : ℂ, a < s.re →
          UnequalRankConverges ψ (normalizedAbsoluteValue F.canonicalTopologicalData) 1 k
            μbase (rectangularMeasure ν.val 1 (t + 1)) (rankCastWhittaker ψ hrB W₀) W' s) →
        ∃ W₁ ∈ whittakerSet ψ r π,
          ∃ W'' ∈ inverseWhittakerSet ψ (1 + t) (rankOneExtensionLowerInduced F t χlift σ₁),
          ∃ c : ℂ, c ≠ 0 ∧ ∃ a' : ℝ, ∀ s : ℂ, a' < s.re →
            UnequalRankConverges ψ (normalizedAbsoluteValue F.canonicalTopologicalData) 0 k
              μind (rectangularMeasure ν.val 0 ((1 + t) + 1))
              (rankCastWhittaker ψ hrI W₁) W'' s ∧
            unequalRankIntegral ψ (normalizedAbsoluteValue F.canonicalTopologicalData) 0 k
                μind (rectangularMeasure ν.val 0 ((1 + t) + 1))
                (rankCastWhittaker ψ hrI W₁) W'' s =
              c * unequalRankIntegral ψ (normalizedAbsoluteValue F.canonicalTopologicalData)
                1 k μbase (rectangularMeasure ν.val 1 (t + 1))
                (rankCastWhittaker ψ hrB W₀) W' s := by
  intro χlift
  let T := F.canonicalTopologicalData
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel F.Carrier
  have : BorelSpace F.Carrier := ⟨rfl⟩
  let := borel (Langlands.GeneralLinear (t + 1) F.Carrier)
  have : BorelSpace (Langlands.GeneralLinear (t + 1) F.Carrier) := ⟨rfl⟩
  let := borel (upperUnipotent (t + 1) F.Carrier)
  have : BorelSpace (upperUnipotent (t + 1) F.Carrier) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient t F.Carrier)
  have : BorelSpace (LeftUnipotentQuotient t F.Carrier) := ⟨rfl⟩
  let := borel (Langlands.GeneralLinear ((1 + t) + 1) F.Carrier)
  have : BorelSpace (Langlands.GeneralLinear ((1 + t) + 1) F.Carrier) := ⟨rfl⟩
  let := borel (upperUnipotent ((1 + t) + 1) F.Carrier)
  have : BorelSpace (upperUnipotent ((1 + t) + 1) F.Carrier) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient (1 + t) F.Carrier)
  have : BorelSpace (LeftUnipotentQuotient (1 + t) F.Carrier) := ⟨rfl⟩
  let := borel (lowerTriangularSubgroup 1 F.Carrier)
  have : BorelSpace (lowerTriangularSubgroup 1 F.Carrier) := ⟨rfl⟩
  have : T2Space F.Carrier := T.fieldT2
  have : SecondCountableTopology F.Carrier := T.secondCountableTopology
  have : SigmaCompactSpace F.Carrier := T.sigmaCompactSpace
  have : IsTopologicalDivisionRing F.Carrier := inferInstance
  have : SigmaFinite ν.val.measure := inferInstance
  intro _ _ μbase μind hbase hind W₀ hW₀ W' hW' hconv
  obtain rfl : r = (1 + (t + 1)) + k := by omega
  have : SigmaFinite μbase := padic_quotient_sigmaFinite T t μbase hbase.regular
  have : SigmaFinite (rectangularMeasure ν.val 1 (t + 1)) := inferInstance
  have hc : 1 + (t + 1) = (1 + t) + 1 := by omega
  have hre : ∀ g : Langlands.GeneralLinear (1 + (t + 1)) F.Carrier,
      reindex (R := F.Carrier) (finCongr hc) g = g := fun g =>
    Units.ext (Matrix.ext fun _ _ => rfl)
  -- The data of the proof.
  obtain ⟨ℓπ, hW₀m⟩ := hW₀
  obtain ⟨ℓ, hW'm⟩ := hW'
  obtain ⟨a₀, hconv⟩ := hconv
  let f₂ : (coefficientModel π ℓπ).toSubmodule := ⟨W₀, hW₀m⟩
  obtain ⟨w, hw⟩ := modelMap_surjective σ₁ ℓ ⟨W', hW'm⟩
  have hW'g : ∀ g, W'.val g = ℓ.val (σ₁ g w) := by
    intro g
    rw [show W' = (modelMap σ₁ ℓ w).val from congrArg Subtype.val hw.symm]
    rfl
  obtain ⟨U, -, -, f₁, hUc, hUo, -, hU1, hU0, hUabs, -, -, -, -, -, -, -, hin, hout⟩ :=
    rankOneExtensionScalarCutoff p F ψ ν t k V π hπ ℓπ f₂ χ Set.univ isOpen_univ
      (Set.mem_univ _)
  obtain ⟨v₁, hv₁⟩ := modelMap_surjective π ℓπ f₁
  obtain ⟨φ, sec, -, hφint, hφ1, hsec, -, hfix⟩ :=
    rankOneExtensionCompactSection p F ψ ν t k π σ₁ χ v₁ w hπ hσ Set.univ isOpen_univ
      (Set.mem_univ _)
  obtain ⟨Λ, hΛ⟩ := hJ p F t χ σ₁ ψ ℓ ν
  obtain ⟨ρ, -, hρσ, hρpos, hρc, hρinv, C, hC, htransfer⟩ :=
    rankOneExtensionDisintegration_of_statement hdis p F t ν.val μbase μind hbase hind
  let M := rankOneExtensionLowerModel F t χ σ₁
  let W'' : InverseWhittakerFunctions ψ (1 + t) := coefficientMap M Λ (M.asModuleEquiv sec)
  have hW''c : Continuous fun g : Langlands.GeneralLinear (1 + (t + 1)) F.Carrier =>
      W''.val g :=
    continuous_rankOneExtensionLowerCoefficient F χ σ₁ ψ Λ sec
  -- The cutoff set in the lower-triangular group.
  let U' : Set (lowerTriangularSubgroup 1 F.Carrier) := lowerScalarEntry ⁻¹' U
  have hU'o : IsOpen U' := hUo.preimage continuous_lowerScalarEntry
  have hU'ρ : ρ U' ≠ ∞ := (isCompact_preimage_lowerScalarEntry hUc hU0).measure_lt_top.ne
  have hU'pos : 0 < ρ U' := hU'o.measure_pos ρ ⟨1, by simpa [U'] using hU1⟩
  have hc0 : (C : ℂ) * (ρ.real U' : ℂ) ≠ 0 := by
    have hpos : 0 < ρ.real U' := ENNReal.toReal_pos hU'pos.ne' hU'ρ
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr hC.ne') (Complex.ofReal_ne_zero.mpr hpos.ne')
  refine ⟨f₁.val, ⟨ℓπ, f₁.property⟩, W'', ⟨Λ, M.asModuleEquiv sec, rfl⟩,
    (C : ℂ) * (ρ.real U' : ℂ), hc0, a₀, fun s hs => ?_⟩
  -- The scalar measure on `K` and the modulus character.
  have hχm : Measurable (T.normalizedAbsHom : F.Carrier → ℝ≥0) :=
    T.continuous_normalizedAbsHom.measurable
  have hχ : ∀ a : F.Carrier, a ≠ 0 →
      ν.val.measure.map (fun x => a * x) = (T.normalizedAbsHom a)⁻¹ • ν.val.measure :=
    fun a ha => padicScalarHaarScaling F T ν.val.measure (Units.mk0 a ha)
  have : NullSingletonClass ν.val.measure := by
    refine nullSingletonClass_of_map_mul ν.val.measure T.normalizedAbsHom T.uniformizer
      (LocalFactor.PadicAbelian.uniformizerUnit T).ne_zero ?_
      (hχ _ (LocalFactor.PadicAbelian.uniformizerUnit T).ne_zero)
    intro h1
    have h := LocalFactor.PadicAbelian.uniformizerUnit_zpow_abs T 1
    rw [zpow_one, LocalFactor.PadicAbelian.uniformizerUnit_coe, ← PadicField.TopologicalData.normalizedAbsHom_coe, h1,
      NNReal.coe_one, zpow_neg_one] at h
    have hq : (1 : ℝ) < T.residueCardinality := by exact_mod_cast T.residueCardinality_gt_one
    have hq1 : (T.residueCardinality : ℝ) = 1 := by
      rw [← _root_.inv_inj, inv_one]
      exact h.symm
    linarith
  have hD : ∀ g : Langlands.GeneralLinear (t + 1) F.Carrier,
      lowerBlockQuotientDensity T (t + 1) 1 (Quotient.mk _ g) =
        (((T.normalizedAbsHom g.val.det)⁻¹ : ℝ≥0) : ℝ≥0∞) := by
    intro g
    have hne : T.normalizedAbsHom (Matrix.det g.val) ≠ 0 :=
      (map_ne_zero T.normalizedAbsHom).mpr (Matrix.GeneralLinearGroup.det_ne_zero g)
    rw [lowerBlockQuotientDensity_mk, ENNReal.coe_inv hne, ← ENNReal.ofReal_coe_nnreal,
      PadicField.TopologicalData.normalizedAbsHom_coe]
    simp only [Nat.cast_one, zpow_neg_one]
  have hχU : ∀ h ∈ U', T.normalizedAbsHom (lowerScalarEntry h) = 1 := fun h hh =>
    NNReal.eq (by rw [NNReal.coe_one]; exact hUabs _ hh)
  -- The functions of the change of variables.
  let H := rankOneExtensionUnfoldingFunction ψ (normalizedAbsoluteValue T) f₁.val
    (rankOneExtensionLowerSectionCoefficient F t χ σ₁ ψ ℓ sec) (s - ((0 + k + 1 : ℕ) : ℂ) / 2)
  let fQ : LeftUnipotentQuotient (1 + t) F.Carrier → ℂ :=
    unequalRankIntegrand ψ (normalizedAbsoluteValue T) 0 k (rankCastWhittaker ψ hrI f₁.val)
      W'' s 0
  let fB : LeftUnipotentQuotient t F.Carrier × Matrix (Fin 1) (Fin (t + 1)) F.Carrier → ℂ :=
    fun qx => unequalRankIntegrand ψ (normalizedAbsoluteValue T) 1 k
      (rankCastWhittaker ψ hrB W₀) W' s qx.2 qx.1
  have hfQ_mk : ∀ g : Langlands.GeneralLinear (1 + (t + 1)) F.Carrier,
      fQ (Quotient.mk _ (reindex (R := F.Carrier) (finCongr hc) g)) =
        f₁.val.val (rankInclusion (k + 1) g) * W''.val g *
          determinantWeight (normalizedAbsoluteValue T) g (s - ((0 + k + 1 : ℕ) : ℂ) / 2) :=
    fun g => (unequalRankIntegrand_rankCast_zero_mk ψ _ hrI hc f₁.val W'' s 0 g).trans
      (by rw [hre])
  have hfQc : Continuous fQ := by
    have hlift : Continuous fun g : Langlands.GeneralLinear ((1 + t) + 1) F.Carrier =>
        fQ (Quotient.mk _ g) := by
      have heq : (fun g : Langlands.GeneralLinear ((1 + t) + 1) F.Carrier =>
          fQ (Quotient.mk _ g)) =
          rankOneExtensionUnfoldingFunction ψ (normalizedAbsoluteValue T) f₁.val
            (fun g => W''.val g) (s - ((0 + k + 1 : ℕ) : ℂ) / 2) := by
        funext g
        conv_lhs => rw [← hre g]
        exact hfQ_mk g
      rw [heq]
      exact continuous_rankOneExtensionUnfoldingFunction_of_continuous F ψ π hπ ℓπ f₁ _
        hW''c _
    exact isQuotientMap_quotient_mk'.continuous_iff.mpr hlift
  have htr : Integrable (fQ ∘ rankOneExtensionQuotientChart)
      ((μbase.withDensity (lowerBlockQuotientDensity T (t + 1) 1)).prod
        ((rectangularMeasure ν.val 1 (t + 1)).prod ρ)) →
      Integrable fQ μind ∧ ∫ q, fQ q ∂μind = (C : ℂ) * ∫ z, fQ (rankOneExtensionQuotientChart z)
        ∂((μbase.withDensity (lowerBlockQuotientDensity T (t + 1) 1)).prod
          ((rectangularMeasure ν.val 1 (t + 1)).prod ρ)) := by
    intro hi
    obtain ⟨hiff, hint⟩ := htransfer fQ hfQc.measurable
    have hQ := hiff.2 hi
    exact ⟨hQ, hint hQ⟩
  have hJcore : ∀ (g : Langlands.GeneralLinear (t + 1) F.Carrier)
      (x : Matrix (Fin 1) (Fin (t + 1)) F.Carrier) (h : lowerTriangularSubgroup 1 F.Carrier),
      Integrable (fun y => H (rankOneExtensionUpperCell t y *
        rankOneExtensionLowerBlock t g (x 0) (lowerScalarUnit h)))
          (Measure.pi fun _ => ν.val.measure) →
      fQ (rankOneExtensionQuotientChart (Quotient.mk _ g, (x, h))) =
        ∫ y, H (rankOneExtensionUpperCell t y *
          rankOneExtensionLowerBlock t g (x 0) (lowerScalarUnit h))
            ∂(Measure.pi fun _ => ν.val.measure) := by
    intro g x h hint
    rw [rankOneExtensionQuotientChart_mk hc]
    change fQ (Quotient.mk _ (reindex (R := F.Carrier) (finCongr hc)
      (rankOneExtensionLowerBlock t g (x 0) (lowerScalarUnit h)))) = _
    rw [hfQ_mk]
    have hV : Integrable (rankOneExtensionStableIntegrand F t χ σ₁ ψ ℓ sec
          (rankOneExtensionLowerBlock t g (x 0) (lowerScalarUnit h)))
          (Measure.pi fun _ => ν.val.measure) →
        W''.val (rankOneExtensionLowerBlock t g (x 0) (lowerScalarUnit h)) =
          ∫ y, rankOneExtensionStableIntegrand F t χ σ₁ ψ ℓ sec
            (rankOneExtensionLowerBlock t g (x 0) (lowerScalarUnit h)) y
            ∂(Measure.pi fun _ => ν.val.measure) :=
      hΛ sec _
    have hHy : ∀ y, H (rankOneExtensionUpperCell t y *
        rankOneExtensionLowerBlock t g (x 0) (lowerScalarUnit h)) =
        (f₁.val.val (rankInclusion (k + 1)
            (rankOneExtensionLowerBlock t g (x 0) (lowerScalarUnit h))) *
          determinantWeight (normalizedAbsoluteValue T)
            (rankOneExtensionLowerBlock t g (x 0) (lowerScalarUnit h))
            (s - ((0 + k + 1 : ℕ) : ℂ) / 2)) *
          rankOneExtensionStableIntegrand F t χ σ₁ ψ ℓ sec
            (rankOneExtensionLowerBlock t g (x 0) (lowerScalarUnit h)) y :=
      fun y => rankOneExtensionUnfoldingFunction_upperCell_mul ψ _ f₁.val _ _ y _
    simp only [hHy] at hint ⊢
    rw [← mul_eq_integral_of_integrable_mul _ _ _ _ hV hint]
    ring
  have hWc : ∀ (g : Langlands.GeneralLinear (t + 1) F.Carrier)
      (x : Matrix (Fin 1) (Fin (t + 1)) F.Carrier) (h : lowerTriangularSubgroup 1 F.Carrier)
      (y : Fin (t + 1) → F.Carrier),
      H (rankOneExtensionLowerBlock t g (x 0) (lowerScalarUnit h) *
          rankOneExtensionUpperCell t y) =
        U'.indicator (fun _ => (1 : ℂ)) h * fB (Quotient.mk _ g, x) * φ y := by
    intro g x h y
    have h1 := rankOneExtensionUnfoldingFunction_lowerBlock_mul_upperCell F ψ χ π ℓπ f₁ f₂ v₁
      hv₁ U hUabs hin hout σ₁ ℓ w sec φ hsec hfix s g (x 0) (lowerScalarUnit h) y
    have h2 : fB (Quotient.mk _ g, x) =
        f₂.val.val (rankOneExtensionEmbeddedLowerBlock t k g (x 0) 1) * ℓ.val (σ₁ g w) *
          determinantWeight (normalizedAbsoluteValue T) g (s - ((1 + k + 1 : ℕ) : ℂ) / 2) := by
      rw [← hW'g g]
      exact unequalRankIntegrand_rankCast_one_mk ψ _ hrB W₀ W' s x g
    have h3 : U.indicator (fun _ => (1 : ℂ)) ((lowerScalarUnit h : F.Carrierˣ) : F.Carrier) =
        U'.indicator (fun _ => (1 : ℂ)) h := rfl
    rw [h2, ← h3]
    exact h1
  obtain ⟨hQint, hQeq⟩ := rankOneExtensionUnfoldingCore (K := F.Carrier) (t := t) μbase
    hbase.right_invariant (rectangularMeasure ν.val 1 (t + 1)) ρ ν.val.measure
    T.normalizedAbsHom hχm hχ (lowerBlockQuotientDensity T (t + 1) 1)
    (measurable_lowerBlockQuotientDensity T (t + 1) 1) hD μind rankOneExtensionQuotientChart
    (C : ℂ) fQ htr H
    (continuous_rankOneExtensionUnfoldingFunction F ψ χ π hπ ℓπ f₁ σ₁ ℓ sec _)
    (rankOneExtensionUnfoldingFunction_lowerBlock_mul ψ _ f₁.val _
      (fun n z => rankOneExtensionLowerSectionCoefficient_unipotent_mul F t χ σ₁ ψ ℓ sec n z) _)
    hJcore fB (hconv s hs) φ hφint U' hU'o.measurableSet hU'ρ hχU hWc
  have hφ1' : ∫ y, φ y ∂(Measure.pi fun _ => ν.val.measure) = 1 := hφ1
  rw [hφ1', mul_one] at hQeq
  refine ⟨?_, ?_⟩
  · change Integrable (fun qx => unequalRankIntegrand ψ (normalizedAbsoluteValue T) 0 k
        (rankCastWhittaker ψ hrI f₁.val) W'' s qx.2 qx.1)
        (μind.prod (rectangularMeasure ν.val 0 ((1 + t) + 1)))
    have hfun : (fun qx : LeftUnipotentQuotient (1 + t) F.Carrier ×
        Matrix (Fin 0) (Fin ((1 + t) + 1)) F.Carrier =>
        unequalRankIntegrand ψ (normalizedAbsoluteValue T) 0 k
          (rankCastWhittaker ψ hrI f₁.val) W'' s qx.2 qx.1) = fun qx => fQ qx.1 := by
      funext qx
      rw [Subsingleton.elim qx.2 0]
    rw [hfun, rectangularMeasure_zero_rows]
    exact hQint.comp_fst _
  · have hB : ∫ z, fB z ∂(μbase.prod (rectangularMeasure ν.val 1 (t + 1))) =
        ∫ q, ∫ x, unequalRankIntegrand ψ (normalizedAbsoluteValue T) 1 k
          (rankCastWhittaker ψ hrB W₀) W' s x q ∂(rectangularMeasure ν.val 1 (t + 1)) ∂μbase :=
      integral_prod fB (hconv s hs)
    change ∫ q, ∫ x, unequalRankIntegrand ψ (normalizedAbsoluteValue T) 0 k
        (rankCastWhittaker ψ hrI f₁.val) W'' s x q ∂(rectangularMeasure ν.val 0 ((1 + t) + 1))
          ∂μind =
      (C : ℂ) * (ρ.real U' : ℂ) * ∫ q, ∫ x, unequalRankIntegrand ψ (normalizedAbsoluteValue T)
        1 k (rankCastWhittaker ψ hrB W₀) W' s x q ∂(rectangularMeasure ν.val 1 (t + 1)) ∂μbase
    rw [← hB, rectangularMeasure_zero_rows]
    simp only [integral_dirac_of_subsingleton]
    exact hQeq

end Pointwise

section Conditional

/-- `RankOneExtensionSpanComparisonStatement` from the lower-block disintegration of the
quotient measure and the lower Jacquet functional. -/
theorem rankOneExtensionSpanComparison_of_statements
    (hdis : LowerBlockQuotientDisintegrationStatement.{uF})
    (hJ : RankOneExtensionLowerJacquetFunctionalStatement.{uF, uW}) :
    RankOneExtensionSpanComparisonStatement.{uF, uV, uW} := by
  intro p _ F ψ ν r t V _ _ W _ _ π σ₁ χ hrt hπ hσ χlift hrBase hrInd _ _ μbase μind hbase hind
  exact rankOneExtensionSpanComparison_of_pointwise p F ψ ν r t (r - t - 2) π σ₁ χ hrBase hrInd
    μbase μind (rankOneExtensionSpanComparison_pointwise hdis hJ p F ψ ν r t (r - t - 2) π σ₁ χ
      hrBase hrInd hπ.1.1 hσ.1.1 μbase μind hbase hind)

end Conditional

end Langlands.RankinSelberg
