import Langlands.Representation.RankinSelberg.TwoBlockDominantOppositeDeformation
import Langlands.AllField.Representation.RankinSelberg.TwoBlockSecondWhittakerDeformationProof
noncomputable section
set_option maxHeartbeats 1600000

namespace Langlands.AllField.RankinSelberg.DominantRankTransport
open Langlands.RankinSelberg.DominantRankTransport hiding OppositeWhittakerFamilyData ambient_mul_firstBlock_eq_opposite complexOppositeTwistBlocks complexOppositeTwistInduced exists_oppositeWhittakerFamily exists_opposite_coefficient firstBlockZeroComparison oppositeDeformationTopology oppositeTwistComparison
open Langlands.AllField.RankinSelberg.DominantRankTransport
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement NormalizedProductWhittakerTypeStatement QuotientHaarExistenceStatement TwoBlockJacquetConvergenceStatement TwoBlockSecondWhittakerDeformationStatement TwoBlockWhittakerDeformationStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement determinantComplexPower_upperUnipotent isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedProductWhittakerType twoBlockDeformedBlocks twoBlockDeformedBlocks_zero twoBlockDeformedInduced twoBlockOppositeTwistBlocks twoBlockOppositeTwistBlocks_apply twoBlockOppositeTwistBlocks_isOfWhittakerType_iff twoBlockOppositeTwistFunctional twoBlockOppositeTwistFunctional_val twoBlockSecondDeformedBlocks twoBlockSecondDeformedBlocks_zero twoBlockSecondDeformedInduced twoBlockSecondWhittakerDeformation twoBlockWhittakerDeformation
open Langlands.AllField.RankinSelberg

open Langlands.HarmonicAnalysis hiding padicRectangularHaarScaling padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis
open Langlands.Whittaker hiding CompactLocalizationStatement MirabolicUnitTestStatement TwoBlockCellUnipotentStabilityStatement TwoBlockInducedCarrier UnipotentOrbitStatement compactLocalization exchangedParabolic functionalsCongr hasCompactSupport_twoBlockCellRestriction inducedLocalization_of_prerequisites mirabolicUnitTest mul_upperUnipotent_mem_twoBlockCell swapRank_exchangedParabolic twoBlockCell twoBlockCellInclusion twoBlockCellInclusion_apply twoBlockCellPoint twoBlockCellPoint_mul_upperUnipotent twoBlockCellRestriction twoBlockCellSubmodule twoBlockCellUnipotentStability twoBlockEval twoBlockInduced twoBlockInducingRepresentation twoBlockParabolic twoBlockRestriction unipotentLeviFactor unipotentOrbit unipotentShift
open Langlands.AllField.Whittaker
open Langlands.GeneralLinear hiding upperUnipotentCompactContainment upperUnipotent_isLimitOfCompactSubgroups
open Langlands.AllField.GeneralLinear
open Langlands.RankinSelberg.TwoBlockSecondDeformation hiding ambientCharacter ambient_mul_firstBlock_eq_secondBlock analyticAt_twistedFamily determinantComplexPower_oppositeParabolic exists_level_twistedFamily exists_second_coefficient secondCoefficient_of_firstCoefficient twistComparison zeroComparison
open Langlands.AllField.RankinSelberg.TwoBlockSecondDeformation

universe uF uW

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

variable {t : ℕ} (m : Fin 2 → ℕ) (h : ∑ i, (m i + 1) = t + 1)
  {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
  (σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F) (W i))

/-- The complex extension of the actual opposite real twist family. -/
abbrev complexOppositeTwistBlocks (u : ℂ) :
    ∀ i, Representation ℂ (GeneralLinear (m i + 1) F) (W i) :=
  fun i => Langlands.twist
    ((⟨⟩ : LocalFieldData F).determinantComplexPower (m i + 1)
      (if i = 0 then -u else u)) (σ i)

abbrev complexOppositeTwistInduced (u : ℂ) :=
  Langlands.AllField.RankinSelberg.TwoBlockJacquet.inducedRep F h (complexOppositeTwistBlocks F m σ u)

/-- The ambient determinant twist and the first-block twist combine on the
actual lower parabolic, including its original ordered Levi coordinates. -/
theorem ambient_mul_firstBlock_eq_opposite (u : ℂ)
    (q : (succBlockShape m h).oppositeParabolic F) :
    (⟨⟩ : LocalFieldData F).determinantComplexPower (t + 1) u
        (q : GeneralLinear (t + 1) F) *
      ∏ i, (⟨⟩ : LocalFieldData F).determinantComplexPower (m i + 1)
        (if i = 0 then -2 * u else 0)
        ((succBlockShape m h).oppositeLeviProjection F q i) =
      ∏ i, (⟨⟩ : LocalFieldData F).determinantComplexPower (m i + 1)
        (if i = 0 then -u else u)
        ((succBlockShape m h).oppositeLeviProjection F q i) := by
  rw [determinantComplexPower_oppositeParabolic]
  simp only [Fin.prod_univ_two, Fin.isValue, ↓reduceIte, one_ne_zero,
    Langlands.LocalFieldData.determinantComplexPower_zero, MonoidHom.one_apply, mul_one]
  have h0 :
      (⟨⟩ : LocalFieldData F).determinantComplexPower (m 0 + 1) u
          ((succBlockShape m h).oppositeLeviProjection F q 0) *
        (⟨⟩ : LocalFieldData F).determinantComplexPower (m 0 + 1) (-2 * u)
          ((succBlockShape m h).oppositeLeviProjection F q 0) =
      (⟨⟩ : LocalFieldData F).determinantComplexPower (m 0 + 1) (-u)
          ((succBlockShape m h).oppositeLeviProjection F q 0) := by
    rw [← MonoidHom.mul_apply, ← Langlands.LocalFieldData.determinantComplexPower_add]
    congr 2
    ring
  calc
    _ = ((⟨⟩ : LocalFieldData F).determinantComplexPower (m 0 + 1) u
          ((succBlockShape m h).oppositeLeviProjection F q 0) *
        (⟨⟩ : LocalFieldData F).determinantComplexPower (m 0 + 1) (-2 * u)
          ((succBlockShape m h).oppositeLeviProjection F q 0)) *
        (⟨⟩ : LocalFieldData F).determinantComplexPower (m 1 + 1) u
          ((succBlockShape m h).oppositeLeviProjection F q 1) := by ac_rfl
    _ = _ := by rw [h0]

/-- An actual lower-induced equivalence, obtained by multiplying sections by
`|det|^u` and comparing the complete covariance actions. -/
def oppositeTwistComparison (u : ℂ) :
    (Langlands.twist ((⟨⟩ : LocalFieldData F).determinantComplexPower (t + 1) u)
      (twoBlockDeformedInduced F m h σ (-2 * u))).Equiv
      (complexOppositeTwistInduced F m h σ u) :=
  haveI := (⟨⟩ : LocalFieldData F).generalLinearTopologicalGroup (t + 1)
  (Induction.smoothInductionTwistEquiv ((succBlockShape m h).oppositeParabolic F)
    (ambientCharacter F u)
    (Langlands.twist
      ((⟨⟩ : LocalFieldData F).oppositeParabolicHalfModulus (succBlockShape m h))
      (((succBlockShape m h).blockTensor (twoBlockDeformedBlocks F m σ (-2 * u))).comp
        ((succBlockShape m h).oppositeLeviProjection F)))).trans
    (Induction.smoothInducedEquiv ((succBlockShape m h).oppositeParabolic F)
      (inducingEquivOfApply (fun q x => by
        change ((⟨⟩ : LocalFieldData F).determinantComplexPower (t + 1) u
              (q : GeneralLinear (t + 1) F) : ℂ) •
            (((⟨⟩ : LocalFieldData F).oppositeParabolicHalfModulus (succBlockShape m h) q :
                ℂ) •
              (succBlockShape m h).blockTensor (twoBlockDeformedBlocks F m σ (-2 * u))
                ((succBlockShape m h).oppositeLeviProjection F q) x) =
          ((⟨⟩ : LocalFieldData F).oppositeParabolicHalfModulus (succBlockShape m h) q :
              ℂ) •
            (succBlockShape m h).blockTensor (complexOppositeTwistBlocks F m σ u)
              ((succBlockShape m h).oppositeLeviProjection F q) x
        have key := congrArg Units.val (ambient_mul_firstBlock_eq_opposite F m h u q)
        rw [Units.val_mul] at key
        rw [blockTensor_twist_apply (succBlockShape m h)
            (fun i => (⟨⟩ : LocalFieldData F).determinantComplexPower (m i + 1)
              (if i = 0 then -2 * u else 0)) σ,
          blockTensor_twist_apply (succBlockShape m h)
            (fun i => (⟨⟩ : LocalFieldData F).determinantComplexPower (m i + 1)
              (if i = 0 then -u else u)) σ,
          ← key, mul_smul]
        exact smul_comm _ _ _)))

/-- Identity coordinates at zero between the first-block family and the
original actual lower induction. -/
def firstBlockZeroComparison :
    (twoBlockDeformedInduced F m h σ 0).Equiv (Langlands.AllField.RankinSelberg.TwoBlockJacquet.inducedRep F h σ) :=
  haveI := (⟨⟩ : LocalFieldData F).generalLinearTopologicalGroup (t + 1)
  Induction.smoothInducedEquiv ((succBlockShape m h).oppositeParabolic F)
    (inducingEquivOfApply (fun q x => by
      change ((⟨⟩ : LocalFieldData F).oppositeParabolicHalfModulus (succBlockShape m h) q :
            ℂ) •
          (succBlockShape m h).blockTensor (twoBlockDeformedBlocks F m σ 0)
            ((succBlockShape m h).oppositeLeviProjection F q) x =
        ((⟨⟩ : LocalFieldData F).oppositeParabolicHalfModulus (succBlockShape m h) q :
            ℂ) •
          (succBlockShape m h).blockTensor σ
            ((succBlockShape m h).oppositeLeviProjection F q) x
      rw [twoBlockDeformedBlocks_zero]))

/-- Functional/vector transport along the actual opposite-twist comparison. -/
theorem exists_opposite_coefficient (ψ : UnitaryAdditiveCharacter F) (u : ℂ)
    (ell : glInverseFunctionals ψ t (twoBlockDeformedInduced F m h σ (-2 * u)))
    (hell : ell.val ≠ 0) (v) :
    ∃ ell' : glInverseFunctionals ψ t (complexOppositeTwistInduced F m h σ u),
      ell'.val ≠ 0 ∧ ∃ v', ∀ g,
        ((⟨⟩ : LocalFieldData F).determinantComplexPower (t + 1) u g : ℂ) *
          ell.val (twoBlockDeformedInduced F m h σ (-2 * u) g v) =
        ell'.val (complexOppositeTwistInduced F m h σ u g v') := by
  let E := oppositeTwistComparison F m h σ u
  let ell2 := twistFunctional (upperUnipotent (t + 1) F)
    (inverseStandardCharacter ψ t)
    ((⟨⟩ : LocalFieldData F).determinantComplexPower (t + 1) u)
    (determinantComplexPower_upperUnipotent F (t + 1) u) _ ell
  refine ⟨Whittaker.functionalsCongr E ell2, functionalsCongr_val_ne_zero E ell2 hell,
    E v, fun g => ?_⟩
  rw [functionalsCongr_val_rep]
  change _ = ell.val (((⟨⟩ : LocalFieldData F).determinantComplexPower (t + 1) u g : ℂ) •
    twoBlockDeformedInduced F m h σ (-2 * u) g v)
  rw [map_smul, smul_eq_mul]

/-- Every supplied lower-induced model coefficient extends to an actual
opposite-twist inverse Whittaker family with one compact open right level. -/
def OppositeWhittakerFamilyData (ψ : UnitaryAdditiveCharacter F)
    (U : ℂ → InverseWhittakerFunctions ψ t) : Prop :=
  (∀ u : ℂ, ∃ ell : glInverseFunctionals ψ t (complexOppositeTwistInduced F m h σ u),
    ell.val ≠ 0 ∧ ∃ v, coefficientMap (complexOppositeTwistInduced F m h σ u) ell v = U u) ∧
  (∃ K : Subgroup (GeneralLinear (t + 1) F),
    IsOpen (K : Set (GeneralLinear (t + 1) F)) ∧
    IsCompact (K : Set (GeneralLinear (t + 1) F)) ∧
    ∀ (u : ℂ) (g : GeneralLinear (t + 1) F) (k : K),
      (U u).val (g * k) = (U u).val g) ∧
  ∀ (g : GeneralLinear (t + 1) F) (u : ℂ),
    AnalyticAt ℂ (fun z => (U z).val g) u

theorem exists_oppositeWhittakerFamily
    (ψ : UnitaryAdditiveCharacter F)
    (hσ : ∀ i, IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (σ i))
    (ell0 : glInverseFunctionals ψ t (Langlands.AllField.RankinSelberg.TwoBlockJacquet.inducedRep F h σ))
    (hell0 : ell0.val ≠ 0)
    (Z : (coefficientModel (Langlands.AllField.RankinSelberg.TwoBlockJacquet.inducedRep F h σ) ell0).toSubmodule) :
    ∃ U : ℂ → InverseWhittakerFunctions ψ t, U 0 = Z.val ∧
      OppositeWhittakerFamilyData F m h σ ψ U := by
  obtain ⟨v0, hv0⟩ := modelMap_surjective (Langlands.AllField.RankinSelberg.TwoBlockJacquet.inducedRep F h σ) ell0 Z
  let E0 := firstBlockZeroComparison F m h σ
  let ellS := (Whittaker.functionalsCongr E0).symm ell0
  obtain ⟨V, hV0, hVu, hVK, hVa⟩ := twoBlockWhittakerDeformation F ψ t m h σ hσ
    ellS (functionalsCongr_symm_val_ne_zero E0 ell0 hell0) (E0.symm v0)
  let Vu : ℂ → GeneralLinear (t + 1) F → ℂ := fun u g =>
    ((⟨⟩ : LocalFieldData F).determinantComplexPower (t + 1) u g : ℂ) * V (-2 * u) g
  have hcoeff : ∀ u : ℂ,
      ∃ ell : glInverseFunctionals ψ t (complexOppositeTwistInduced F m h σ u),
        ell.val ≠ 0 ∧ ∃ v, ∀ g, Vu u g =
          ell.val (complexOppositeTwistInduced F m h σ u g v) := by
    intro u
    obtain ⟨ell, hell, v, hv⟩ := hVu (-2 * u)
    obtain ⟨ell', hell', v', hv'⟩ := exists_opposite_coefficient F m h σ ψ u ell hell v
    exact ⟨ell', hell', v', fun g => by dsimp only [Vu]; rw [hv]; exact hv' g⟩
  let U : ℂ → InverseWhittakerFunctions ψ t := fun u =>
    ⟨Vu u, by
      obtain ⟨ell, -, v, hv⟩ := hcoeff u
      intro n g
      change Vu u ((n : GeneralLinear (t + 1) F) * g) =
        (inverseStandardCharacter ψ t n : ℂ) * Vu u g
      rw [hv, hv, map_mul, Module.End.mul_apply]
      exact ell.property n _⟩
  refine ⟨U, ?_, ?_, ?_, ?_⟩
  · apply Subtype.ext
    funext g
    change ((⟨⟩ : LocalFieldData F).determinantComplexPower (t + 1) 0 g : ℂ) *
      V (-2 * 0) g = Z.val.val g
    rw [Langlands.LocalFieldData.determinantComplexPower_zero, MonoidHom.one_apply,
      Units.val_one, one_mul, mul_zero, hV0 g,
      functionalsCongr_symm_val_rep E0 ell0 g v0]
    exact congrArg (fun z => z.val.val g) hv0
  · intro u
    obtain ⟨ell, hell, v, hv⟩ := hcoeff u
    refine ⟨ell, hell, v, ?_⟩
    apply Subtype.ext
    funext g
    exact (hv g).symm
  · have hVK2 : ∃ K : Subgroup (GeneralLinear (t + 1) F),
        IsOpen (K : Set (GeneralLinear (t + 1) F)) ∧
        IsCompact (K : Set (GeneralLinear (t + 1) F)) ∧
        ∀ (u : ℂ) (g : GeneralLinear (t + 1) F) (k : K),
          V (2 * u) (g * k) = V (2 * u) g := by
      obtain ⟨K, hKo, hKc, hK⟩ := hVK
      exact ⟨K, hKo, hKc, fun u g k => hK (2 * u) g k⟩
    simpa only [U, Vu, mul_neg, neg_mul] using
      exists_level_twistedFamily F (fun u g => V (2 * u) g) hVK2
  · intro g u
    have hVa2 : ∀ (g : GeneralLinear (t + 1) F) (u : ℂ),
        AnalyticAt ℂ (fun z => V (2 * z) g) u := by
      intro g u
      exact (hVa g (2 * u)).comp_of_eq (analyticAt_const.mul analyticAt_id) rfl
    simpa only [U, Vu, mul_neg, neg_mul] using
      analyticAt_twistedFamily F (fun u g => V (2 * u) g) hVa2 g u

end Langlands.AllField.RankinSelberg.DominantRankTransport
