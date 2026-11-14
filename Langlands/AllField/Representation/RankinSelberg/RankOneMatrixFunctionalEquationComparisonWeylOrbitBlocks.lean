import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonWeylOrbitBlocks
import Langlands.AllField.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonFourierInvariance
import Langlands.AllField.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonWeylBlockFourier
/-! The scalar Fourier orbit and complementary block orbit for the same matrix test. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement QuotientHaarExistenceStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement determinantNorm_rankOneSignedBlockWeyl normalizedAbsoluteValue normalizedAbsoluteValue_apply orbitBlocksBorel orbitBlocksLocalField orbitBlocksMeasurable orbitBlocksNBorel orbitBlocksNLocallyCompact orbitBlocksNMeasurable orbitBlocksNSecondCountable orbitBlocksSecondCountable orbitBlocksSigmaCompact orbitBlocksT2 orbitBlocksTopology orbitBlocksTotallyDisconnected orbitBlocksValuativeRel signedWeylOrbit_blockOrbit_fourier_duality signedWeylOrbit_blockOrbit_fourier_duality_averaged signedWeyl_affineBlock_fourier_duality unequalRankFiniteExpansion weylBlockBorelSpace weylBlockLocalField weylBlockMeasurableSpace weylBlockNBorelSpace weylBlockNLocallyCompact weylBlockNMeasurableSpace weylBlockNSecondCountable weylBlockSecondCountable weylBlockSigmaCompact weylBlockT2 weylBlockTopology weylBlockTotallyDisconnected weylBlockValuativeRel
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory MeasureTheory.Measure
open Langlands.GeneralLinear
open Langlands.HarmonicAnalysis hiding padicRectangularFourierIntegral_leftRight padicRectangularHaarScaling padicRectangularLeftRight_measurePreserving padicScalarHaarScaling padicUnipotentHaar_iota_fourier_duality_right
open Langlands.AllField.HarmonicAnalysis
open Langlands.Whittaker
open Langlands.RankinSelberg.UnequalRankComplementaryConjugationProof

universe uK

variable {K : Type uK} [Field K]

section Kernels


end Kernels

section CanonicalPadic

variable (F : Type uK) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance orbitBlocksT2 : T2Space F := (⟨⟩ : LocalFieldData F).fieldT2
local instance orbitBlocksSecondCountable : SecondCountableTopology F :=
  (⟨⟩ : LocalFieldData F).secondCountableTopology
local instance orbitBlocksSigmaCompact : SigmaCompactSpace F :=
  (⟨⟩ : LocalFieldData F).sigmaCompactSpace
local instance orbitBlocksMeasurable : MeasurableSpace F := borel _
local instance orbitBlocksBorel : BorelSpace F := ⟨rfl⟩
local instance orbitBlocksNMeasurable (n : ℕ) :
    MeasurableSpace (upperUnipotent (n + 1) F) := borel _
local instance orbitBlocksNBorel (n : ℕ) :
    BorelSpace (upperUnipotent (n + 1) F) := ⟨rfl⟩
local instance orbitBlocksNLocallyCompact (n : ℕ) :
    LocallyCompactSpace (upperUnipotent (n + 1) F) :=
  (upperEntryCoordinates (n + 1) (K := F)).isClosedEmbedding.locallyCompactSpace
local instance orbitBlocksNSecondCountable (n : ℕ) :
    SecondCountableTopology (upperUnipotent (n + 1) F) :=
  (upperEntryCoordinates (n + 1) (K := F)).secondCountableTopology
local instance orbitBlocksTotallyDisconnected : TotallyDisconnectedSpace F := by
  let : NonarchimedeanRing F := by
    convert! ValuativeRel.nonarchimedeanRing F
    exact Valuation.toTopologicalSpace_eq _
  infer_instance

/-- The signed complementary Weyl matrix has normalized determinant norm one. -/
theorem determinantNorm_rankOneSignedBlockWeyl (n : ℕ) (hn : 0 < n) :
    (⟨⟩ : LocalFieldData F).determinantNorm (n + 1)
      (rankOneSignedBlockWeyl n hn) = 1 := by
  have hA : (⟨⟩ : LocalFieldData F).determinantNorm (n + 1)
      (rankOneWeylAlternating n) = 1 := by
    apply (⟨⟩ : LocalFieldData F).determinantNorm_eq_one_of_pow_eq_one _
      (by decide : 2 ≠ 0)
    rw [pow_two, rankOneWeylAlternating_mul_self]
  have hE : (⟨⟩ : LocalFieldData F).determinantNorm (n + 1)
      (rankOneWeylLeadingSign n) = 1 := by
    apply (⟨⟩ : LocalFieldData F).determinantNorm_eq_one_of_pow_eq_one _
      (by decide : 2 ≠ 0)
    rw [pow_two, rankOneWeylLeadingSign_mul_self]
  simp only [rankOneSignedBlockWeyl, map_mul, hA, hE, blockWeylAt_eq,
    (⟨⟩ : LocalFieldData F).determinantNorm_permutation, one_mul]

private theorem scalarSign_preserving (ν : AdditiveHaarMeasure F) (d : ℕ) :
    MeasurePreserving (fun a : F => (-1 : F) ^ d * a)
      ν.measure ν.measure := by
  rcases neg_one_pow_eq_or F d with hd | hd
  · convert! MeasurePreserving.id ν.measure using 1
    funext a
    simp [hd]
  · simpa only [hd, neg_one_mul] using measurePreserving_neg ν.measure

private def scalarSignEquiv (d : ℕ) : F ≃ᵐ F where
  toFun a := (-1 : F) ^ d * a
  invFun a := (-1 : F) ^ d * a
  left_inv a := by
    change (-1 : F) ^ d * ((-1 : F) ^ d * a) = a
    rw [← mul_assoc, ← mul_pow]
    simp
  right_inv a := by
    change (-1 : F) ^ d * ((-1 : F) ^ d * a) = a
    rw [← mul_assoc, ← mul_pow]
    simp
  measurable_toFun := measurable_const.mul measurable_id
  measurable_invFun := measurable_const.mul measurable_id

set_option maxHeartbeats 800000 in
/-- For the same test and norm-one h, the true scalar Fourier orbit and
complementary block orbit are jointly integrable and have equal integrals.
The scalar sign substitution preserves the supplied additive Haar exactly. -/
theorem signedWeylOrbit_blockOrbit_fourier_duality
    (ψ : UnitaryAdditiveCharacter F) (ν : AdditiveHaarMeasure F)
    (hsd : IsSelfDual ψ ν) (m : ℕ)
    (h : Langlands.GeneralLinear (m + 2) F)
    (hh : (⟨⟩ : LocalFieldData F).determinantNorm (m + 2) h = 1)
    (Φ : SchwartzBruhat (Matrix (Fin (m + 2)) (Fin (m + 2)) F)) :
    Integrable (signedWeylOrbitFourierKernel ψ ν m h Φ)
      ((unipotentHaar F (m + 1)).prod ν.measure) ∧
    Integrable (signedBlockOrbitKernel ψ m h Φ)
      ((unipotentHaar F (m + 1)).prod
        (ν.measure.prod (rectangularMeasure ν m 1))) ∧
    (∫ z, signedWeylOrbitFourierKernel ψ ν m h Φ z
      ∂(unipotentHaar F (m + 1)).prod ν.measure) =
    ∫ z, signedBlockOrbitKernel ψ m h Φ z
      ∂(unipotentHaar F (m + 1)).prod
        (ν.measure.prod (rectangularMeasure ν m 1)) := by
  let b : Langlands.GeneralLinear (m + 2) F :=
    rankOneSignedBlockWeyl (m + 1) (by omega)
  have hbh : (⟨⟩ : LocalFieldData F).determinantNorm (m + 2) (b * h) = 1 := by
    rw [map_mul, determinantNorm_rankOneSignedBlockWeyl, hh, one_mul]
  obtain ⟨hl, hr, he⟩ := signedWeyl_affineBlock_fourier_duality F ψ ν hsd m
    (b * h) hbh Φ
  let e := (MeasurableEquiv.refl (upperUnipotent (m + 2) F)).prodCongr
    (scalarSignEquiv F (m + 2))
  have hp : MeasurePreserving e
      ((unipotentHaar F (m + 1)).prod ν.measure)
      ((unipotentHaar F (m + 1)).prod ν.measure) :=
    (MeasurePreserving.id _).prod (scalarSign_preserving F ν (m + 2))
  have hleft (z : upperUnipotent (m + 2) F × F) :
      signedWeylScalarFourierKernel ψ ν m (b * h) Φ z =
        signedWeylOrbitFourierKernel ψ ν m h Φ (e z) := by
    change signedWeylScalarFourierKernel ψ ν m (b * h) Φ z =
      signedWeylOrbitFourierKernel ψ ν m h Φ
        (z.1, (-1 : F) ^ (m + 2) * z.2)
    have hc : b⁻¹.val * (b * h).val = h.val := by
      change (b⁻¹ * (b * h)).val = h.val
      rw [inv_mul_cancel_left]
    simp only [signedWeylScalarFourierKernel, signedWeylOrbitFourierKernel,
      inverseTranspose_coe, Subgroup.coe_inv, Matrix.mul_assoc]
    change _ * rectangularFourierIntegral ψ ν Φ
      (_ * (_ * (_ * (b⁻¹.val * (b * h).val)))) = _
    rw [hc]
  have hright (z : upperUnipotent (m + 2) F ×
      (F × Matrix (Fin m) (Fin 1) F)) :
      affineBlockFourierKernel ψ m (b * h) Φ z =
        signedBlockOrbitKernel ψ m h Φ z := by
    simp only [affineBlockFourierKernel, signedBlockOrbitKernel, map_mul,
      b, inverseTranspose_rankOneSignedBlockWeyl, Units.val_mul, Matrix.mul_assoc]
  have hl' : Integrable ((signedWeylOrbitFourierKernel ψ ν m h Φ) ∘ e)
      ((unipotentHaar F (m + 1)).prod ν.measure) :=
    hl.congr (Filter.Eventually.of_forall hleft)
  refine ⟨(hp.integrable_comp_emb e.measurableEmbedding).mp hl',
    hr.congr (Filter.Eventually.of_forall hright), ?_⟩
  calc
    _ = ∫ z, signedWeylScalarFourierKernel ψ ν m (b * h) Φ z
        ∂(unipotentHaar F (m + 1)).prod ν.measure := by
      rw [← hp.integral_comp e.measurableEmbedding]
      exact integral_congr_ae (Filter.Eventually.of_forall fun z => (hleft z).symm)
    _ = _ := he
    _ = _ := integral_congr_ae (Filter.Eventually.of_forall hright)

/-- Fubini puts the scalar outside the actual Fourier orbit and the
scalar/block pair outside the original orbit, with genuine convergence. -/
theorem signedWeylOrbit_blockOrbit_fourier_duality_averaged
    (ψ : UnitaryAdditiveCharacter F) (ν : AdditiveHaarMeasure F)
    (hsd : IsSelfDual ψ ν) (m : ℕ)
    (h : Langlands.GeneralLinear (m + 2) F)
    (hh : (⟨⟩ : LocalFieldData F).determinantNorm (m + 2) h = 1)
    (Φ : SchwartzBruhat (Matrix (Fin (m + 2)) (Fin (m + 2)) F)) :
    Integrable (fun a : F =>
      ∫ u, signedWeylOrbitFourierKernel ψ ν m h Φ (u, a)
        ∂unipotentHaar F (m + 1)) ν.measure ∧
    Integrable (fun z : F × Matrix (Fin m) (Fin 1) F =>
      ∫ u, signedBlockOrbitKernel ψ m h Φ (u, z)
        ∂unipotentHaar F (m + 1))
      (ν.measure.prod (rectangularMeasure ν m 1)) ∧
    (∫ a : F, ∫ u, signedWeylOrbitFourierKernel ψ ν m h Φ (u, a)
      ∂unipotentHaar F (m + 1) ∂ν.measure) =
    ∫ a : F, ∫ X : Matrix (Fin m) (Fin 1) F,
      ∫ u, signedBlockOrbitKernel ψ m h Φ (u, (a, X))
        ∂unipotentHaar F (m + 1)
      ∂rectangularMeasure ν m 1 ∂ν.measure := by
  obtain ⟨hl, hr, he⟩ :=
    signedWeylOrbit_blockOrbit_fourier_duality F ψ ν hsd m h hh Φ
  refine ⟨hl.integral_prod_right, hr.integral_prod_right, ?_⟩
  rw [integral_prod_symm _ hl, integral_prod_symm _ hr] at he
  exact he.trans (integral_prod _ hr.integral_prod_right)

end CanonicalPadic

end Langlands.AllField.RankinSelberg
