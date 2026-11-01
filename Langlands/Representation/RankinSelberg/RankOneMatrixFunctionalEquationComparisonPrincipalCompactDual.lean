import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonCompactGLParameters
import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonSignedCompactPairing
import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonPrincipalWeighted

/-! Compact principal extraction of the actual signed complementary block. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis GeneralLinear Whittaker Induction Topology
open RankOneIwasawa RankOneBox CompactWhittakerSynthesis Conductor
open scoped NNReal ENNReal

universe uF uX
variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance principalCompactDualTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance principalCompactDualValuativeRel : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance principalCompactDualLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance principalCompactDualT2 : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance principalCompactDualSecondCountable : SecondCountableTopology F.Carrier :=
  F.canonicalTopologicalData.secondCountableTopology
local instance principalCompactDualMeasurable : MeasurableSpace F.Carrier := borel _
local instance principalCompactDualBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance principalCompactDualNMeasurable (n : ℕ) :
    MeasurableSpace (upperUnipotent (n + 1) F.Carrier) := borel _
local instance principalCompactDualNBorel (n : ℕ) :
    BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
local instance principalCompactDualNLocallyCompact (n : ℕ) :
    LocallyCompactSpace (upperUnipotent (n + 1) F.Carrier) :=
  F.canonicalTopologicalData.upperUnipotentLocallyCompactSpace (n + 1)
local instance principalCompactDualGLMeasurable (n : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := borel _
local instance principalCompactDualGLBorel (n : ℕ) :
    BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
local instance principalCompactDualGLLocallyCompact (n : ℕ) :
    LocallyCompactSpace (Langlands.GeneralLinear (n + 1) F.Carrier) :=
  F.canonicalTopologicalData.generalLinearLocallyCompactSpace (n + 1)
local instance principalCompactDualGLSecondCountable (n : ℕ) :
    SecondCountableTopology (Langlands.GeneralLinear (n + 1) F.Carrier) :=
  F.canonicalTopologicalData.generalLinearSecondCountableTopology (n + 1)
local instance principalCompactDualNSecondCountable (n : ℕ) :
    SecondCountableTopology (upperUnipotent (n + 1) F.Carrier) :=
  Topology.IsEmbedding.subtypeVal.secondCountableTopology
local instance principalCompactDualTotallyDisconnected : TotallyDisconnectedSpace F.Carrier := by
  let : NonarchimedeanRing F.Carrier := by
    convert! ValuativeRel.nonarchimedeanRing F.Carrier
    exact Valuation.toTopologicalSpace_eq _
  infer_instance

local instance principalCompactDualUnitsMeasurable : MeasurableSpace F.Carrierˣ := borel _
local instance principalCompactDualUnitsBorel : BorelSpace F.Carrierˣ := ⟨rfl⟩
local instance principalCompactDualUnitsSecondCountable : SecondCountableTopology F.Carrierˣ :=
  Units.isEmbedding_val₀.secondCountableTopology

local notation "abv" => normalizedAbsoluteValue F.canonicalTopologicalData

/-- The compact principal subgroup indicator is retained until convergence
has been proved on the full product. -/
def principalCompactKernel (n a : ℕ) :
    SchwartzBruhat (Langlands.GeneralLinear (n + 1) F.Carrier) :=
  ⟨(principalLevelOpenSubgroup F.Carrier n a :
        Set (Langlands.GeneralLinear (n + 1) F.Carrier)).indicator (fun _ => (1 : ℂ)),
    by
      classical
      let S := (principalLevelOpenSubgroup F.Carrier n a :
        Set (Langlands.GeneralLinear (n + 1) F.Carrier))
      have hs : IsClopen S := (principalLevelOpenSubgroup F.Carrier n a).isClopen
      refine (IsLocallyConstant.iff_eventually_eq _).2 fun x => ?_
      by_cases hx : x ∈ S
      · filter_upwards [hs.isOpen.mem_nhds hx] with y hy
        rw [Set.indicator_of_mem hy, Set.indicator_of_mem hx]
      · filter_upwards [hs.isClosed.isOpen_compl.mem_nhds hx] with y hy
        rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx],
    HasCompactSupport.intro (isCompact_principalLevelOpenSubgroup F.Carrier n a)
      (fun _ hx => Set.indicator_of_notMem hx _)⟩

@[simp] theorem principalCompactKernel_of_mem (n a : ℕ)
    {k : Langlands.GeneralLinear (n + 1) F.Carrier}
    (hk : k ∈ principalLevelSubgroup F.Carrier n a) :
    principalCompactKernel F n a k = 1 := by
  change (principalLevelOpenSubgroup F.Carrier n a :
        Set (Langlands.GeneralLinear (n + 1) F.Carrier)).indicator
    (fun _ => (1 : ℂ)) k = 1
  exact Set.indicator_of_mem hk _

theorem principalCompactKernel_ae (n a : ℕ) (C : ℝ) :
    ∀ᵐ k ∂principalAveragingMeasure F (n := n) a C,
      principalCompactKernel F n a k = 1 := by
  filter_upwards [principalAveragingMeasure_ae_mem F a C] with k hk
  exact principalCompactKernel_of_mem F n a hk

theorem principalCompactKernel_detNorm (n a : ℕ)
    (k : Langlands.GeneralLinear (n + 1) F.Carrier)
    (hk : principalCompactKernel F n a k ≠ 0) :
    F.canonicalTopologicalData.determinantNorm (n + 1) k = 1 := by
  have hmem : k ∈ principalLevelSubgroup F.Carrier n a := by
    by_contra hn
    apply hk
    change (principalLevelOpenSubgroup F.Carrier n a :
        Set (Langlands.GeneralLinear (n + 1) F.Carrier)).indicator
      (fun _ => (1 : ℂ)) k = 0
    exact Set.indicator_of_notMem hn _
  apply Units.ext
  apply NNReal.eq
  have h := abv_det_eq_one F (principalLevel_le_integral F a hmem)
  exact h

/-- The literal complementary-block evaluation point, with its actual signed
block Weyl factor and inverse transpose of the averaging parameter. -/
def principalSignedBlockPoint (m : ℕ)
    (k : Langlands.GeneralLinear (m + 2) F.Carrier)
    (z : Langlands.GeneralLinear 1 F.Carrier × Matrix (Fin m) (Fin 1) F.Carrier) :
    Langlands.GeneralLinear (m + 2) F.Carrier :=
  AdjacentBlockReduction.blockMatrixAt m 0 (by omega) z.1 z.2 *
    rankOneSignedBlockWeyl (m + 1) (by omega) *
    inverseTranspose (m + 2) F.Carrier k

/-- The actual principal compact dual block restriction, before averaging. -/
def principalCompactDualIntegrand (ψ : UnitaryAdditiveCharacter F.Carrier)
    (m : ℕ)
    (f : CompactFunctions (upperUnipotent (m + 2) F.Carrier)
      (characterRepresentation (standardCharacter ψ (m + 1))))
    (z : Langlands.GeneralLinear (m + 2) F.Carrier ×
      (Langlands.GeneralLinear 1 F.Carrier × Matrix (Fin m) (Fin 1) F.Carrier)) : ℂ :=
  eval _ _ f.val (principalSignedBlockPoint F m z.1 z.2)

/-- The real GL1 density is the corresponding complex determinant power. -/
theorem glOneWeight_eq_determinantWeight (n : ℕ)
    (g : Langlands.GeneralLinear 1 F.Carrier) :
    ((weight F n (g, 1) : ℝ) : ℂ) = determinantWeight abv g (-(n : ℂ)) := by
  rw [weight_glOne]
  simp only [determinantWeight, Complex.cpow_neg, Complex.cpow_natCast,
    NNReal.coe_inv, NNReal.coe_pow, Complex.ofReal_inv, Complex.ofReal_pow,
    F.canonicalTopologicalData.normalizedAbsUnits_coe,
    Matrix.GeneralLinearGroup.val_det_apply, normalizedAbsoluteValue_apply]

/-- Natural ambient weight and the GL1 density leave exponent one. -/
theorem glOneWeight_smul_natSucc (n : ℕ)
    (g : Langlands.GeneralLinear 1 F.Carrier) (z : ℂ) :
    weight F n (g, 1) • (determinantWeight abv g (n + 1 : ℕ) * z) =
      determinantWeight abv g 1 * z := by
  rw [NNReal.smul_def, Complex.real_smul, glOneWeight_eq_determinantWeight,
    ← mul_assoc]
  have hg : determinantWeight abv g (-(n : ℂ)) *
      determinantWeight abv g (n + 1 : ℕ) = determinantWeight abv g 1 := by
    unfold determinantWeight
    rw [← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr
      ((normalizedAbsoluteValue F.canonicalTopologicalData).ne_zero
        (Matrix.GeneralLinearGroup.det_ne_zero g)))]
    congr 1
    push_cast
    ring
  rw [hg]

/-- The block restriction preserves the scalar determinant norm when the
principal averaging parameter has norm one. -/
theorem determinantWeight_principalSignedBlockPoint (m : ℕ)
    (k : Langlands.GeneralLinear (m + 2) F.Carrier)
    (hk : F.canonicalTopologicalData.determinantNorm (m + 2) k = 1)
    (z : Langlands.GeneralLinear 1 F.Carrier × Matrix (Fin m) (Fin 1) F.Carrier)
    (s : ℂ) :
    determinantWeight abv (principalSignedBlockPoint F m k z) s =
      determinantWeight abv z.1 s := by
  have hB : abv (Matrix.det (rankOneSignedBlockWeyl (m + 1)
      (K := F.Carrier) (by omega)).val) = 1 := by
    have hb := determinantNorm_rankOneSignedBlockWeyl F (m + 1) (by omega)
    have hb' := congrArg (fun t : ℝ≥0ˣ => ((t : ℝ≥0) : ℝ)) hb
    exact hb'
  have hki : abv (Matrix.det (inverseTranspose (m + 2) F.Carrier k).val) = 1 := by
    have hk' : F.canonicalTopologicalData.determinantNorm (m + 2)
        (inverseTranspose (m + 2) F.Carrier k) = 1 := by
      rw [F.canonicalTopologicalData.determinantNorm_inverseTranspose, hk, inv_one]
    exact congrArg (fun t : ℝ≥0ˣ => ((t : ℝ≥0) : ℝ)) hk'
  have hd : Matrix.det (AdjacentBlockReduction.blockMatrixAt (n := 0) (r := m + 1) m 0
      (by omega) z.1 z.2).val = Matrix.det z.1.val := by
    rw [← firstColumnMatrix_eq_blockMatrixAt, det_firstColumnMatrix]
    simp only [rankOneAffineParameters_zero, Matrix.det_fin_one]
  simp only [principalSignedBlockPoint, determinantWeight, Units.val_mul,
    Matrix.det_mul, map_mul, hB, hki, hd, mul_one]

/-- Reconstruction is pointwise; its full-product use below is justified by
the previously proved parameter convergence. -/
theorem principalCompactDualIntegrand_reconstruct
    (ψ : UnitaryAdditiveCharacter F.Carrier) (m a : ℕ)
    (f : CompactFunctions (upperUnipotent (m + 2) F.Carrier)
      (characterRepresentation (standardCharacter ψ (m + 1))))
    (k : Langlands.GeneralLinear (m + 2) F.Carrier)
    (hk : F.canonicalTopologicalData.determinantNorm (m + 2) k = 1)
    (hκ : principalCompactKernel F (m + 1) a k = 1)
    (z : Langlands.GeneralLinear 1 F.Carrier × Matrix (Fin m) (Fin 1) F.Carrier) :
    weight F (m + 1) (z.1, 1) • principalCompactDualIntegrand F ψ m f (k, z) =
      signedBlockGLParameterIntegrand F ψ m id (principalCompactKernel F (m + 1) a)
        (weightedCompactMatrixLift F ψ (m + 1) (m + 2 : ℕ) f) (k, z) := by
  have he := weightedCompactMatrixLift_orbit F ψ (m + 1) (m + 2 : ℕ) f
    (principalSignedBlockPoint F m k z)
  rw [determinantWeight_principalSignedBlockPoint F m k hk] at he
  change weight F (m + 1) (z.1, 1) •
    eval _ _ f.val (principalSignedBlockPoint F m k z) = _
  rw [← he, glOneWeight_smul_natSucc]
  simp only [signedBlockGLParameterIntegrand, hκ, one_mul, id_eq,
    signedBlockOrbitKernel_at_generalLinear, principalSignedBlockPoint, mul_assoc]


/-- The natural scalar Fourier orbit has exactly the density used by the
joint Fourier/block identity. -/
theorem principalCompactFourier_reconstruct
    (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier)
    (hsd : IsSelfDual ψ ν) (m a : ℕ)
    (f : CompactFunctions (upperUnipotent (m + 2) F.Carrier)
      (characterRepresentation (standardCharacter ψ (m + 1))))
    (k : Langlands.GeneralLinear (m + 2) F.Carrier)
    (hk : F.canonicalTopologicalData.determinantNorm (m + 2) k = 1)
    (hκ : principalCompactKernel F (m + 1) a k = 1)
    (g : Langlands.GeneralLinear 1 F.Carrier) :
    weight F (m + 1) (g, 1) •
      signedFourierOrbitOfCompact F ψ ν hsd (m + 1) f (rankOneEmbedding m g * k) =
      signedWeylGLParameterIntegrand F ψ ν m id (principalCompactKernel F (m + 1) a)
        (weightedCompactMatrixLift F ψ (m + 1) (m + 2 : ℕ) f) (k, g) := by
  have hknorm : abv (Matrix.det k.val) = 1 :=
    congrArg (fun t : ℝ≥0ˣ => ((t : ℝ≥0) : ℝ)) hk
  unfold signedFourierOrbitOfCompact weightedSignedMatrixOrbit
  rw [determinantWeight_mul_of_norm_one F _ k hknorm,
    determinantWeight_rankOneEmbedding, glOneWeight_smul_natSucc]
  simp only [signedMatrixOrbit, signedWeylGLParameterIntegrand,
    signedWeylOrbitFourierKernel, rectangularFourierEquiv_apply,
    hκ, one_mul, id_eq, Units.val_mul, rankOneEmbedding_val, Matrix.mul_assoc]

private theorem measurable_glOneWeight (n : ℕ) :
    Measurable (fun g : Langlands.GeneralLinear 1 F.Carrier => weight F n (g, 1)) :=
  (continuous_weight F n).measurable.comp (measurable_id.prodMk measurable_const)

/-- Retaining a parameter commutes with passing to the actual weighted
GL1 measure. -/
theorem parameter_glOneMeasure_density {X : Type uX} [MeasurableSpace X]
    (μ : Measure X) [SFinite μ] (n : ℕ) :
    μ.prod (glOneMeasure F n) =
      (μ.prod (generalLinearHaar F.Carrier 0)).withDensity
        (fun z => (weight F n (z.2, 1) : ℝ≥0∞)) := by
  exact prod_withDensity_right
    (measurable_glOneWeight F n).coe_nnreal_ennreal

/-- Both the compact parameter and the complementary block commute with
the true weighted GL1 measure, before any averaging. -/
theorem parameter_glOneMeasure_block_density {X : Type uX} [MeasurableSpace X]
    (μ : Measure X) [SFinite μ] (ν : AdditiveHaarMeasure F.Carrier) (m : ℕ) :
    μ.prod ((glOneMeasure F (m + 1)).prod (rectangularMeasure ν m 1)) =
      (μ.prod ((generalLinearHaar F.Carrier 0).prod (rectangularMeasure ν m 1))).withDensity
        (fun z => (weight F (m + 1) (z.2.1, 1) : ℝ≥0∞)) := by
  unfold glOneMeasure
  rw [prod_withDensity_left
    (measurable_glOneWeight F (m + 1)).coe_nnreal_ennreal]
  exact prod_withDensity_right
    ((measurable_glOneWeight F (m + 1)).coe_nnreal_ennreal.comp measurable_fst)

/-- The compact principal parameter remains in the full complementary-block
integral: no cancellation inside its average is used for convergence. -/
theorem principalCompactDual_fourierOrbit_duality
    (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier)
    (hsd : IsSelfDual ψ ν) (m a : ℕ) (C : ℝ)
    (f : CompactFunctions (upperUnipotent (m + 2) F.Carrier)
      (characterRepresentation (standardCharacter ψ (m + 1)))) :
    let μ := principalAveragingMeasure F (n := m + 1) a C
    Integrable (fun z : Langlands.GeneralLinear (m + 2) F.Carrier ×
        Langlands.GeneralLinear 1 F.Carrier =>
      signedFourierOrbitOfCompact F ψ ν hsd (m + 1) f (rankOneEmbedding m z.2 * z.1))
      (μ.prod (glOneMeasure F (m + 1))) ∧
    Integrable (principalCompactDualIntegrand F ψ m f)
      (μ.prod ((glOneMeasure F (m + 1)).prod (rectangularMeasure ν m 1))) ∧
    (∫ z : Langlands.GeneralLinear (m + 2) F.Carrier × Langlands.GeneralLinear 1 F.Carrier,
      signedFourierOrbitOfCompact F ψ ν hsd (m + 1) f (rankOneEmbedding m z.2 * z.1)
      ∂μ.prod (glOneMeasure F (m + 1))) =
    ∫ z, principalCompactDualIntegrand F ψ m f z
      ∂μ.prod ((glOneMeasure F (m + 1)).prod (rectangularMeasure ν m 1)) := by
  dsimp only
  let μ := principalAveragingMeasure F (n := m + 1) a C
  let Φ := weightedCompactMatrixLift F ψ (m + 1) (m + 2 : ℕ) f
  let κ := principalCompactKernel F (m + 1) a
  let L := fun z : Langlands.GeneralLinear (m + 2) F.Carrier ×
      Langlands.GeneralLinear 1 F.Carrier =>
    signedFourierOrbitOfCompact F ψ ν hsd (m + 1) f (rankOneEmbedding m z.2 * z.1)
  obtain ⟨hl, hr, he⟩ := signedWeylGL_blockGL_parameter_duality F μ ψ ν hsd m
    id continuous_id κ (principalCompactKernel_detNorm F (m + 1) a) Φ
  have hwL : Measurable (fun z : Langlands.GeneralLinear (m + 2) F.Carrier ×
      Langlands.GeneralLinear 1 F.Carrier => weight F (m + 1) (z.2, 1)) :=
    (measurable_glOneWeight F (m + 1)).comp measurable_snd
  have hwR : Measurable (fun z : Langlands.GeneralLinear (m + 2) F.Carrier ×
      (Langlands.GeneralLinear 1 F.Carrier × Matrix (Fin m) (Fin 1) F.Carrier) =>
      weight F (m + 1) (z.2.1, 1)) :=
    (measurable_glOneWeight F (m + 1)).comp (measurable_fst.comp measurable_snd)
  have hlae : (fun z : Langlands.GeneralLinear (m + 2) F.Carrier ×
      Langlands.GeneralLinear 1 F.Carrier => weight F (m + 1) (z.2, 1) • L z)
      =ᵐ[μ.prod (generalLinearHaar F.Carrier 0)]
        signedWeylGLParameterIntegrand F ψ ν m id κ Φ := by
    have hκ := (Measure.quasiMeasurePreserving_fst
      (μ := μ) (ν := generalLinearHaar F.Carrier 0)).ae
      (principalCompactKernel_ae F (m + 1) a C)
    have hk := (Measure.quasiMeasurePreserving_fst
      (μ := μ) (ν := generalLinearHaar F.Carrier 0)).ae
      (principalAveragingMeasure_ae_det_norm F a C)
    filter_upwards [hκ, hk] with z hκ hk
    exact principalCompactFourier_reconstruct F ψ ν hsd m a f z.1
      (by apply Units.ext; apply NNReal.eq; exact hk) hκ z.2
  have hrae : (fun z : Langlands.GeneralLinear (m + 2) F.Carrier ×
      (Langlands.GeneralLinear 1 F.Carrier × Matrix (Fin m) (Fin 1) F.Carrier) =>
      weight F (m + 1) (z.2.1, 1) • principalCompactDualIntegrand F ψ m f z)
      =ᵐ[μ.prod ((generalLinearHaar F.Carrier 0).prod (rectangularMeasure ν m 1))]
        signedBlockGLParameterIntegrand F ψ m id κ Φ := by
    have hκ := (Measure.quasiMeasurePreserving_fst
      (μ := μ) (ν := (generalLinearHaar F.Carrier 0).prod (rectangularMeasure ν m 1))).ae
      (principalCompactKernel_ae F (m + 1) a C)
    have hk := (Measure.quasiMeasurePreserving_fst
      (μ := μ) (ν := (generalLinearHaar F.Carrier 0).prod (rectangularMeasure ν m 1))).ae
      (principalAveragingMeasure_ae_det_norm F a C)
    filter_upwards [hκ, hk] with z hκ hk
    exact principalCompactDualIntegrand_reconstruct F ψ m a f z.1
      (by apply Units.ext; apply NNReal.eq; exact hk) hκ z.2
  have hl' : Integrable L (μ.prod (glOneMeasure F (m + 1))) := by
    rw [parameter_glOneMeasure_density,
      integrable_withDensity_iff_integrable_smul hwL]
    exact hl.congr hlae.symm
  have hr' : Integrable (principalCompactDualIntegrand F ψ m f)
      (μ.prod ((glOneMeasure F (m + 1)).prod (rectangularMeasure ν m 1))) := by
    rw [parameter_glOneMeasure_block_density,
      integrable_withDensity_iff_integrable_smul hwR]
    exact hr.congr hrae.symm
  refine ⟨hl', hr', ?_⟩
  change (∫ z, L z ∂μ.prod (glOneMeasure F (m + 1))) = _
  rw [parameter_glOneMeasure_density,
    integral_withDensity_eq_integral_smul hwL,
    integral_congr_ae hlae, he,
    parameter_glOneMeasure_block_density,
    integral_withDensity_eq_integral_smul hwR]
  exact integral_congr_ae hrae.symm


/-- The fixed lattice test is supported in its actual compact open box. -/
theorem tsupport_boxLatticeTest_subset (n : ℕ) (A q : ℤ) (a : ℕ) :
    tsupport (boxLatticeTest F (n := n) A q a : _ → ℂ) ⊆ box F A q a := by
  apply closure_minimal _ (isCompact_box F A q a).isClosed
  intro X hX
  by_contra hn
  apply hX
  rw [boxLatticeTest_apply, Set.indicator_of_notMem hn]

/-- One original box test and its same principal measure give the actual
signed complementary block identity for every compact Whittaker input, with
both full product convergence and no additional scalar. -/
theorem principalCompactDual_pairing
    (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier)
    (hsd : IsSelfDual ψ ν) {m a : ℕ} (ha : 0 < a)
    (hA : 0 ≤ F.canonicalTopologicalData.additiveConductor ψ + a)
    (f : CompactFunctions (upperUnipotent (m + 2) F.Carrier)
      (characterRepresentation (standardCharacter ψ (m + 1)))) :
    let q := F.canonicalTopologicalData.additiveConductor ψ
    let Ψ := boxLatticeTest F (n := m + 1) (q + a) q a
    let C := boxExtractionConstant F (n := m + 1) (q + a) q a
    let μ := principalAveragingMeasure F (n := m + 1) a C
    Integrable (fun h : Langlands.GeneralLinear (m + 2) F.Carrier =>
      eval _ _ f.val h * rectangularFourierIntegral ψ ν Ψ (rankOneSignedWeyl (m + 1) * h).val)
      (generalLinearHaar F.Carrier (m + 1)) ∧
    Integrable (principalCompactDualIntegrand F ψ m f)
      (μ.prod ((glOneMeasure F (m + 1)).prod (rectangularMeasure ν m 1))) ∧
    (∫ h : Langlands.GeneralLinear (m + 2) F.Carrier,
      eval _ _ f.val h * rectangularFourierIntegral ψ ν Ψ (rankOneSignedWeyl (m + 1) * h).val
      ∂generalLinearHaar F.Carrier (m + 1)) =
    ∫ z, principalCompactDualIntegrand F ψ m f z
      ∂μ.prod ((glOneMeasure F (m + 1)).prod (rectangularMeasure ν m 1)) := by
  dsimp only
  let q := F.canonicalTopologicalData.additiveConductor ψ
  let Ψ := boxLatticeTest F (n := m + 1) (q + a) q a
  let C := boxExtractionConstant F (n := m + 1) (q + a) q a
  let μ := principalAveragingMeasure F (n := m + 1) a C
  let K := signedFourierOrbitOfCompact F ψ ν hsd (m + 1) f
  obtain ⟨hK, hf, hp⟩ := compact_signedFourier_pairing F ψ ν hsd (m + 1) f Ψ
    (q + a) q ha (tsupport_boxLatticeTest_subset F (m + 1) (q + a) q a)
  have hK' : Integrable (fun h : Langlands.GeneralLinear (m + 2) F.Carrier =>
      Ψ h.val * K h) (generalLinearHaar F.Carrier (m + 1)) :=
    hK.congr (g := fun h => Ψ h.val * K h)
      (Filter.Eventually.of_forall fun h => mul_comm (K h) (Ψ h.val))
  obtain ⟨_, hx⟩ := principalMeasure_extraction F ψ ha hA K
    (continuous_signedFourierOrbitOfCompact F ψ ν hsd (m + 1) f)
    (signedFourierOrbitOfCompact_left F ψ ν hsd (m + 1) f) hK'
  obtain ⟨hl, hr, he⟩ := principalCompactDual_fourierOrbit_duality F ψ ν hsd m a C f
  refine ⟨hf, hr, ?_⟩
  calc
    _ = ∫ h, K h * Ψ h.val ∂generalLinearHaar F.Carrier (m + 1) := by
      exact hp.symm
    _ = ∫ h, Ψ h.val * K h ∂generalLinearHaar F.Carrier (m + 1) :=
      integral_congr_ae (Filter.Eventually.of_forall fun h => mul_comm (K h) (Ψ h.val))
    _ = ∫ g, ∫ k, K (rankOneEmbedding m g * k) ∂μ ∂glOneMeasure F (m + 1) := hx
    _ = ∫ z, K (rankOneEmbedding m z.2 * z.1) ∂μ.prod (glOneMeasure F (m + 1)) :=
      (integral_prod_symm _ hl).symm
    _ = _ := he


/-- Determinant twisting takes place on the actual compact group function.
The same original box and same principal measure work for every complex
spectral exponent, with genuine full product convergence. -/
theorem principalCompactDual_pairing_weighted
    (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier)
    (hsd : IsSelfDual ψ ν) {m a : ℕ} (ha : 0 < a)
    (hA : 0 ≤ F.canonicalTopologicalData.additiveConductor ψ + a)
    (f : CompactFunctions (upperUnipotent (m + 2) F.Carrier)
      (characterRepresentation (standardCharacter ψ (m + 1)))) (s : ℂ) :
    let q := F.canonicalTopologicalData.additiveConductor ψ
    let Ψ := boxLatticeTest F (n := m + 1) (q + a) q a
    let C := boxExtractionConstant F (n := m + 1) (q + a) q a
    let μ := principalAveragingMeasure F (n := m + 1) a C
    Integrable (fun h : Langlands.GeneralLinear (m + 2) F.Carrier =>
      (determinantWeight abv h s * eval _ _ f.val h) *
        rectangularFourierIntegral ψ ν Ψ (rankOneSignedWeyl (m + 1) * h).val)
      (generalLinearHaar F.Carrier (m + 1)) ∧
    Integrable (fun z => determinantWeight abv z.2.1 s * principalCompactDualIntegrand F ψ m f z)
      (μ.prod ((glOneMeasure F (m + 1)).prod (rectangularMeasure ν m 1))) ∧
    (∫ h : Langlands.GeneralLinear (m + 2) F.Carrier,
      (determinantWeight abv h s * eval _ _ f.val h) *
        rectangularFourierIntegral ψ ν Ψ (rankOneSignedWeyl (m + 1) * h).val
      ∂generalLinearHaar F.Carrier (m + 1)) =
    ∫ z, determinantWeight abv z.2.1 s * principalCompactDualIntegrand F ψ m f z
      ∂μ.prod ((glOneMeasure F (m + 1)).prod (rectangularMeasure ν m 1)) := by
  dsimp only
  let C := boxExtractionConstant F (n := m + 1)
    (F.canonicalTopologicalData.additiveConductor ψ + a)
    (F.canonicalTopologicalData.additiveConductor ψ) a
  let μ := principalAveragingMeasure F (n := m + 1) a C
  let f' := weightedCompactFunction abv
    (PadicField.TopologicalData.isOpenNormOne_of_eq_normalizedAbs (fun _ => rfl))
    (m + 1) (standardCharacter ψ (m + 1)) (-s) f
  obtain ⟨hi, hj, he⟩ := principalCompactDual_pairing F ψ ν hsd ha hA f'
  have hae : principalCompactDualIntegrand F ψ m f'
      =ᵐ[μ.prod ((glOneMeasure F (m + 1)).prod (rectangularMeasure ν m 1))]
        (fun z => determinantWeight abv z.2.1 s * principalCompactDualIntegrand F ψ m f z) := by
    have hk := (Measure.quasiMeasurePreserving_fst (μ := μ)
      (ν := (glOneMeasure F (m + 1)).prod (rectangularMeasure ν m 1))).ae
      (principalAveragingMeasure_ae_det_norm F a C)
    filter_upwards [hk] with z hz
    simp only [principalCompactDualIntegrand, f', weightedCompactFunction_apply, neg_neg]
    rw [determinantWeight_principalSignedBlockPoint F m z.1
      (by apply Units.ext; apply NNReal.eq; exact hz)]
  refine ⟨?_, hj.congr hae, ?_⟩
  · simpa only [f', weightedCompactFunction_apply, neg_neg] using hi
  · simpa only [f', weightedCompactFunction_apply, neg_neg] using
      he.trans (integral_congr_ae hae)

end Langlands.RankinSelberg
