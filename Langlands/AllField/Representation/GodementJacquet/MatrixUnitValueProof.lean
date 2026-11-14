import Langlands.Representation.GodementJacquet.MatrixUnitValueProof
import Langlands.AllField.Group.GL.CompactOpenSupplement
import Langlands.AllField.Group.GL.NormalizedCharacterSupplement
import Langlands.AllField.Representation.GodementJacquet.MatrixUnitValueStatement
import Langlands.AllField.Representation.RankinSelberg.LastRowCompactOrbitProof
/-! # Construction of a matrix integral equal to one -/

noncomputable section

namespace Langlands.AllField.GodementJacquet
open Langlands.GodementJacquet hiding MatrixUnitValueStatement matrixUnitValue
open Langlands.AllField.GodementJacquet

open _root_.MeasureTheory _root_.Topology
open Langlands.HarmonicAnalysis
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement LastRowCompactOrbitStatement QuotientHaarExistenceStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement lastRowCompactOrbit normalizedAbsoluteValue normalizedAbsoluteValue_apply
open Langlands.AllField.RankinSelberg
open scoped ENNReal NNReal

universe uF uV

namespace Padic
open Langlands.GodementJacquet.Padic hiding IotaMatrixAnalyticAssertions IotaMatrixConvergesOnRight IsMatrixNormalizedGenerator MatrixAnalyticAssertions MatrixConverges MatrixConvergesOnRight MatrixFourierPair NormalizedMatrixFunctionalEquationData exists_biSmoothCoefficient_ne_zero exists_matrixIntegral_one instBorelSpaceGeneralLinearHAddNatOfNatCarrier instBorelSpaceGeneralLinearHAddNatOfNatCarrier_1 instIsNonarchimedeanLocalFieldCarrier instIsNonarchimedeanLocalFieldCarrier_1 instMeasurableSpaceCarrier instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier_1 instTopologicalSpaceCarrier instTopologicalSpaceCarrier_1 instValuativeRelCarrier instValuativeRelCarrier_1 iotaMatrixRationalValues jpssI2 jpssI3 matrixIntegral matrixIntegrand matrixRationalValues matrixUnitValueGLBorel matrixUnitValueGLMeasurable matrixUnitValueLocalField matrixUnitValueT2 matrixUnitValueTopology matrixUnitValueValuation one_mem_iotaMatrixRationalValues one_mem_matrixRationalValues whittakerRationalValues
open Langlands.AllField.GodementJacquet.Padic
open Langlands.GodementJacquet hiding IotaMatrixAnalyticAssertions IotaMatrixConvergesOnRight IsIotaMatrixNormalizedGenerator IsMatrixNormalizedGenerator MatrixAnalyticAssertions MatrixConverges MatrixConvergesOnRight MatrixFourierPair MatrixUnitValueStatement NormalizedMatrixFunctionalEquationData iotaMatrixRationalValues jpssI2 jpssI3 matrixIntegral matrixIntegrand matrixRationalValues matrixUnitValue whittakerRationalValues
open Langlands.AllField.GodementJacquet

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance matrixUnitValueT2 : T2Space F := (⟨⟩ : LocalFieldData F).fieldT2
local instance matrixUnitValueGLMeasurable (n : ℕ) : MeasurableSpace (Langlands.GeneralLinear (n + 1) F) :=
  borel _
local instance matrixUnitValueGLBorel (n : ℕ) : BorelSpace (Langlands.GeneralLinear (n + 1) F) := ⟨rfl⟩

variable {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V] [Nontrivial V]
  (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)

/-- A nonzero smooth representation has a bi-smooth coefficient nonzero at one. -/
theorem exists_biSmoothCoefficient_ne_zero (hσ : IsSmooth σ) :
    ∃ (ℓ : SmoothDual σ) (v : smoothVectors σ), ℓ.val v.val ≠ 0 := by
  let G := Langlands.GeneralLinear (n + 1) F
  have hcofinal : ∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G,
      IsCompact (L : Set G) ∧ L ≤ K := by
    intro K
    obtain ⟨L, hLc, hLK⟩ := (⟨⟩ : LocalFieldData F).generalLinearCompactOpen
      (n + 1) (K : Set G) (K.isOpen.mem_nhds K.one_mem)
    exact ⟨L, hLc, hLK⟩
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have hℓ : ∃ ℓ : SmoothDual σ, ℓ.val v ≠ 0 := by
    by_contra! h
    apply hv
    apply smoothBidual_injective_of_compact_cofinal hcofinal σ hσ
    rw [map_zero]
    apply Subtype.ext
    apply LinearMap.ext
    intro ℓ
    exact h ℓ
  obtain ⟨ℓ, hℓ⟩ := hℓ
  exact ⟨ℓ, ⟨v, hσ v⟩, hℓ⟩

/-- A compact-open test gives an absolutely convergent matrix integral equal to
one for every complex parameter, without any analytic assumption. -/
theorem exists_matrixIntegral_one (hσ : IsSmooth σ) :
    ∃ (Φ : MatrixTestFunction n F) (f : biSmoothMatrixCoefficients σ),
      ∀ s : ℂ, MatrixConverges F Φ s f.val ∧ matrixIntegral F Φ s f.val = 1 := by
  classical
  let T := (⟨⟩ : LocalFieldData F)
  let G := Langlands.GeneralLinear (n + 1) F
  let X := Matrix (Fin (n + 1)) (Fin (n + 1)) F
  let μ := generalLinearHaar F n
  obtain ⟨ℓ, v, hℓv⟩ := exists_biSmoothCoefficient_ne_zero F σ hσ
  obtain ⟨H, hHv⟩ := v.property
  obtain ⟨K, hKc, hKH⟩ := T.generalLinearCompactOpen
    (n + 1) (H : Set G) (H.isOpen.mem_nhds H.one_mem)
  have hKv (k : G) (hk : k ∈ K) : σ k v.val = v.val :=
    hHv ⟨k, hKH hk⟩
  have hdet (k : G) (hk : k ∈ K) : normalizedAbsoluteValue T k.val.det = 1 := by
    have h := T.determinantNorm_eq_one_of_mem_compact (n + 1) K.toSubgroup hKc k hk
    have h' : ((T.determinantNorm (n + 1) k : ℝ≥0) : ℝ) = 1 := by
      rw [h]
      rfl
    exact h'
  let U : Set X := Units.val '' (K : Set G)
  have hUc : IsCompact U := hKc.image Units.continuous_val
  have hUo : IsOpen U :=
    (isOpenEmbedding_generalLinear_val (n + 1)).isOpenMap _ K.isOpen
  have hmem (g : G) : g.val ∈ U ↔ g ∈ K := by
    constructor
    · rintro ⟨k, hk, he⟩
      exact Units.val_injective he ▸ hk
    · intro hg
      exact ⟨g, hg, rfl⟩
  have hKm : MeasurableSet (K : Set G) := K.isOpen.measurableSet
  have hKfin : μ (K : Set G) ≠ ∞ := hKc.measure_lt_top.ne
  have hKpos : μ (K : Set G) ≠ 0 := (K.isOpen.measure_pos μ ⟨1, K.one_mem⟩).ne'
  have hmass : (μ.real (K : Set G) : ℂ) ≠ 0 := by
    rw [Ne, Complex.ofReal_eq_zero, measureReal_def, ENNReal.toReal_eq_zero_iff]
    exact not_or.mpr ⟨hKpos, hKfin⟩
  let c : ℂ := (μ.real (K : Set G) : ℂ)⁻¹
  let Φ : MatrixTestFunction n F :=
    c • Hecke.TestFunction.characteristic ⟨hUc.isClosed, hUo⟩ hUc
  let f : biSmoothMatrixCoefficients σ :=
    (ℓ.val v.val)⁻¹ •
      ⟨biSmoothCoefficient σ ℓ v, Submodule.subset_span ⟨ℓ, v, rfl⟩⟩
  have hf (g : G) (hg : g ∈ K) : f.val g = 1 := by
    change (ℓ.val v.val)⁻¹ * ℓ.val (σ g v.val) = 1
    rw [hKv g hg, inv_mul_cancel₀ hℓv]
  have hpt (s : ℂ) : GodementJacquet.matrixIntegrand
      (normalizedAbsoluteValue T) Φ s f.val =
        (K : Set G).indicator (fun _ => c) := by
    funext g
    by_cases hg : g ∈ K
    · have hΦ : Φ g.val = c := by
        change c * U.indicator (fun _ => (1 : ℂ)) g.val = c
        rw [Set.indicator_of_mem ((hmem g).mpr hg), mul_one]
      simp only [GodementJacquet.matrixIntegrand, hΦ, hf g hg,
        determinantWeight, hdet g hg, Complex.ofReal_one, Complex.one_cpow,
        mul_one, Set.indicator_of_mem hg]
    · have hΦ : Φ g.val = 0 := by
        change c * U.indicator (fun _ => (1 : ℂ)) g.val = 0
        rw [Set.indicator_of_notMem (fun h => hg ((hmem g).mp h)), mul_zero]
      simp only [GodementJacquet.matrixIntegrand, hΦ, zero_mul,
        Set.indicator_of_notMem hg]
  refine ⟨Φ, f, fun s => ⟨?_, ?_⟩⟩
  · change Integrable (GodementJacquet.matrixIntegrand
      (normalizedAbsoluteValue T) Φ s f.val) μ
    rw [hpt]
    exact (integrable_indicator_iff hKm).mpr (integrableOn_const (C := c) hKfin)
  · change (∫ g, GodementJacquet.matrixIntegrand
      (normalizedAbsoluteValue T) Φ s f.val g ∂μ) = 1
    rw [hpt, integral_indicator_const c hKm]
    change (μ.real (K : Set G) : ℂ) * (μ.real (K : Set G) : ℂ)⁻¹ = 1
    exact mul_inv_cancel₀ hmass

/-- The constant rational function one is attained by an actual test and
coefficient, before taking any Laurent span. -/
theorem one_mem_matrixRationalValues (hσ : IsSmooth σ) :
    (1 : RationalFunctions) ∈ matrixRationalValues F σ := by
  obtain ⟨Φ, f, h⟩ := exists_matrixIntegral_one F σ hσ
  refine ⟨Φ, f, ⟨0, fun s _ => (h (s + jpssShift n)).1⟩, 0, ?_⟩
  intro s _
  constructor
  · simp
  · simpa [matrixIntegral] using (h (s + jpssShift n)).2

/-- The inverse-transpose side is the ordinary side of the smooth pullback. -/
theorem one_mem_iotaMatrixRationalValues (hσ : IsSmooth σ) :
    (1 : RationalFunctions) ∈ iotaMatrixRationalValues F σ := by
  unfold iotaMatrixRationalValues
  rw [iotaMatrixRationalValues_eq_comp_inverseTranspose]
  exact one_mem_matrixRationalValues F
    (σ.comp (GeneralLinear.inverseTranspose (n + 1) F).toMonoidHom)
    (isSmooth_comp _ (GeneralLinear.continuous_inverseTranspose _ _) hσ)

end Padic

/-- The unit belongs to both actual matrix rational-value families. -/
theorem matrixUnitValue : MatrixUnitValueStatement.{uF,uV} := by
  intro F _ _ _ _ n V _ _ _ σ hσ
  exact ⟨Langlands.AllField.GodementJacquet.Padic.one_mem_matrixRationalValues F σ hσ,
    Langlands.AllField.GodementJacquet.Padic.one_mem_iotaMatrixRationalValues F σ hσ⟩

end Langlands.AllField.GodementJacquet
