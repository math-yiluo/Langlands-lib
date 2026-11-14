import Langlands.Representation.RankinSelberg.TwoBlockSecondWhittakerDeformationProof
import Langlands.AllField.Representation.RankinSelberg.TwoBlockJacquetConvergence.RadicalIwasawa
import Langlands.AllField.Representation.RankinSelberg.TwoBlockSecondWhittakerDeformationStatement
import Langlands.AllField.Representation.RankinSelberg.TwoBlockWhittakerDeformationProof
/-!
# Proof of the entire standard-character deformation on the second lower block

Proof of `Langlands.AllField.RankinSelberg.TwoBlockSecondWhittakerDeformationStatement`.
The published first-block inverse-character theorem `twoBlockWhittakerDeformation`
is applied with the additive character `ψ.scale (-1)` and evaluated at `-u`. An
actual equivalence between the global twist by `|det|^u` of the first-block family
at `-u` and the second-block family at `u` is constructed on lower-induced sections,
and the coefficients are multiplied by `|det g|^u`.
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement NormalizedProductWhittakerTypeStatement QuotientHaarExistenceStatement TwoBlockJacquetConvergenceStatement TwoBlockSecondWhittakerDeformationStatement TwoBlockWhittakerDeformationStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement determinantComplexPower_upperUnipotent isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedProductWhittakerType twoBlockDeformedBlocks twoBlockDeformedBlocks_zero twoBlockDeformedInduced twoBlockOppositeTwistBlocks twoBlockOppositeTwistBlocks_apply twoBlockOppositeTwistBlocks_isOfWhittakerType_iff twoBlockOppositeTwistFunctional twoBlockOppositeTwistFunctional_val twoBlockSecondDeformedBlocks twoBlockSecondDeformedBlocks_zero twoBlockSecondDeformedInduced twoBlockSecondWhittakerDeformation twoBlockWhittakerDeformation
open Langlands.AllField.RankinSelberg

open Langlands.HarmonicAnalysis hiding padicRectangularHaarScaling padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis
open Langlands.Whittaker hiding CompactLocalizationStatement MirabolicUnitTestStatement TwoBlockCellUnipotentStabilityStatement TwoBlockInducedCarrier UnipotentOrbitStatement compactLocalization exchangedParabolic functionalsCongr hasCompactSupport_twoBlockCellRestriction inducedLocalization_of_prerequisites mirabolicUnitTest mul_upperUnipotent_mem_twoBlockCell swapRank_exchangedParabolic twoBlockCell twoBlockCellInclusion twoBlockCellInclusion_apply twoBlockCellPoint twoBlockCellPoint_mul_upperUnipotent twoBlockCellRestriction twoBlockCellSubmodule twoBlockCellUnipotentStability twoBlockEval twoBlockInduced twoBlockInducingRepresentation twoBlockParabolic twoBlockRestriction unipotentLeviFactor unipotentOrbit unipotentShift
open Langlands.AllField.Whittaker
open Langlands.GeneralLinear hiding upperUnipotentCompactContainment upperUnipotent_isLimitOfCompactSubgroups
open Langlands.AllField.GeneralLinear

universe uF uW

namespace TwoBlockSecondDeformation
open Langlands.RankinSelberg.TwoBlockSecondDeformation hiding ambientCharacter ambient_mul_firstBlock_eq_secondBlock analyticAt_twistedFamily determinantComplexPower_oppositeParabolic exists_level_twistedFamily exists_second_coefficient secondCoefficient_of_firstCoefficient twistComparison zeroComparison
open Langlands.AllField.RankinSelberg.TwoBlockSecondDeformation
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement NormalizedProductWhittakerTypeStatement QuotientHaarExistenceStatement TwoBlockJacquetConvergenceStatement TwoBlockSecondWhittakerDeformationStatement TwoBlockWhittakerDeformationStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement determinantComplexPower_upperUnipotent isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedProductWhittakerType twoBlockDeformedBlocks twoBlockDeformedBlocks_zero twoBlockDeformedInduced twoBlockOppositeTwistBlocks twoBlockOppositeTwistBlocks_apply twoBlockOppositeTwistBlocks_isOfWhittakerType_iff twoBlockOppositeTwistFunctional twoBlockOppositeTwistFunctional_val twoBlockSecondDeformedBlocks twoBlockSecondDeformedBlocks_zero twoBlockSecondDeformedInduced twoBlockSecondWhittakerDeformation twoBlockWhittakerDeformation
open Langlands.AllField.RankinSelberg

section Tensor


end Tensor

section Inducing

universe uG uV


end Inducing

section Transport

universe uR uG uV uW'


end Transport

variable (F : Type uF) [Field F]
variable {t : ℕ} (m : Fin 2 → ℕ) (h : ∑ i, (m i + 1) = t + 1)
variable {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]

private theorem isTopologicalRing [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] :
    IsTopologicalRing F := by
  infer_instance

/-- On the lower block parabolic, `|det|^u` is the product of the block powers
`|det a_i|^u` of its Levi projection. -/
theorem determinantComplexPower_oppositeParabolic [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] (u : ℂ)
    (q : (succBlockShape m h).oppositeParabolic F) :
    (⟨⟩ : LocalFieldData F).determinantComplexPower (t + 1) u
        (q : GeneralLinear (t + 1) F) =
      ∏ i, (⟨⟩ : LocalFieldData F).determinantComplexPower (m i + 1) u
        ((succBlockShape m h).oppositeLeviProjection F q i) := by
  change (⟨⟩ : LocalFieldData F).unramifiedCharacter _
      (determinant (q : GeneralLinear (t + 1) F)) =
    ∏ i, (⟨⟩ : LocalFieldData F).unramifiedCharacter _
      (determinant ((succBlockShape m h).oppositeLeviProjection F q i))
  rw [TwoBlockConvergence.determinant_oppositeParabolic, map_prod]

/-- The ambient twist `|det|^u` combined with the first-block twist `|det|^(-u)`
gives the second-block twist `|det|^u` on every lower parabolic element. -/
theorem ambient_mul_firstBlock_eq_secondBlock [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] (u : ℂ)
    (q : (succBlockShape m h).oppositeParabolic F) :
    (⟨⟩ : LocalFieldData F).determinantComplexPower (t + 1) u
        (q : GeneralLinear (t + 1) F) *
      ∏ i, (⟨⟩ : LocalFieldData F).determinantComplexPower (m i + 1)
        (if i = 0 then -u else 0)
        ((succBlockShape m h).oppositeLeviProjection F q i) =
      ∏ i, (⟨⟩ : LocalFieldData F).determinantComplexPower (m i + 1)
        (if i = 1 then u else 0)
        ((succBlockShape m h).oppositeLeviProjection F q i) := by
  rw [determinantComplexPower_oppositeParabolic]
  simp only [Fin.prod_univ_two, Fin.isValue, ↓reduceIte, one_ne_zero, zero_ne_one,
    Langlands.LocalFieldData.determinantComplexPower_neg,
    Langlands.LocalFieldData.determinantComplexPower_zero, MonoidHom.inv_apply,
    MonoidHom.one_apply, mul_one, one_mul]
  rw [mul_comm ((⟨⟩ : LocalFieldData F).determinantComplexPower (m 0 + 1) u _), mul_assoc,
    mul_inv_cancel, mul_one]

/-- The smooth ambient character `|det|^u` of `GL_(t+1)`. -/
def ambientCharacter [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] (u : ℂ) :
    Induction.SmoothCharacter ℂ (GeneralLinear (t + 1) F) :=
  ⟨(⟨⟩ : LocalFieldData F).determinantComplexPower (t + 1) u,
    (⟨⟩ : LocalFieldData F).isOpen_ker_determinantComplexPower (t + 1) u⟩

/-- The actual comparison of lower-induced representations
`|det|^u ⊗ ρ'_(-u) ≅ ρ_u`, where `ρ'` is the published first-block family and `ρ`
the second-block family: multiplication of sections by `|det|^u`, followed by the
identity on the dependent tensor carrier. -/
def twistComparison [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
    (σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F) (W i)) (u : ℂ) :
    (Langlands.twist ((⟨⟩ : LocalFieldData F).determinantComplexPower (t + 1) u)
      (twoBlockDeformedInduced F m h σ (-u))).Equiv
      (twoBlockSecondDeformedInduced F m h σ u) :=
  haveI := (⟨⟩ : LocalFieldData F).generalLinearTopologicalGroup (t + 1)
  (Induction.smoothInductionTwistEquiv ((succBlockShape m h).oppositeParabolic F)
    (ambientCharacter F u)
    (Langlands.twist
      ((⟨⟩ : LocalFieldData F).oppositeParabolicHalfModulus (succBlockShape m h))
      (((succBlockShape m h).blockTensor (twoBlockDeformedBlocks F m σ (-u))).comp
        ((succBlockShape m h).oppositeLeviProjection F)))).trans
    (Induction.smoothInducedEquiv ((succBlockShape m h).oppositeParabolic F)
      (inducingEquivOfApply (fun q x => by
        change ((⟨⟩ : LocalFieldData F).determinantComplexPower (t + 1) u
              (q : GeneralLinear (t + 1) F) : ℂ) •
            (((⟨⟩ : LocalFieldData F).oppositeParabolicHalfModulus (succBlockShape m h) q :
                ℂ) •
              (succBlockShape m h).blockTensor (twoBlockDeformedBlocks F m σ (-u))
                ((succBlockShape m h).oppositeLeviProjection F q) x) =
          ((⟨⟩ : LocalFieldData F).oppositeParabolicHalfModulus (succBlockShape m h) q :
              ℂ) •
            (succBlockShape m h).blockTensor (twoBlockSecondDeformedBlocks F m σ u)
              ((succBlockShape m h).oppositeLeviProjection F q) x
        have key := congrArg Units.val (ambient_mul_firstBlock_eq_secondBlock F m h u q)
        rw [Units.val_mul] at key
        rw [blockTensor_twist_apply (succBlockShape m h)
            (fun i => (⟨⟩ : LocalFieldData F).determinantComplexPower (m i + 1)
              (if i = 0 then -u else 0)) σ,
          blockTensor_twist_apply (succBlockShape m h)
            (fun i => (⟨⟩ : LocalFieldData F).determinantComplexPower (m i + 1)
              (if i = 1 then u else 0)) σ,
          ← key, mul_smul]
        exact smul_comm _ _ _)))

/-- At parameter zero the two families are the same untwisted induction; this is the
induced equivalence of the identity coordinates. -/
def zeroComparison [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
    (σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F) (W i)) :
    (twoBlockDeformedInduced F m h σ 0).Equiv (twoBlockSecondDeformedInduced F m h σ 0) :=
  haveI := (⟨⟩ : LocalFieldData F).generalLinearTopologicalGroup (t + 1)
  Induction.smoothInducedEquiv ((succBlockShape m h).oppositeParabolic F)
    (inducingEquivOfApply (fun q x => by
      change ((⟨⟩ : LocalFieldData F).oppositeParabolicHalfModulus (succBlockShape m h) q :
            ℂ) •
          (succBlockShape m h).blockTensor (twoBlockDeformedBlocks F m σ 0)
            ((succBlockShape m h).oppositeLeviProjection F q) x =
        ((⟨⟩ : LocalFieldData F).oppositeParabolicHalfModulus (succBlockShape m h) q :
            ℂ) •
          (succBlockShape m h).blockTensor (twoBlockSecondDeformedBlocks F m σ 0)
            ((succBlockShape m h).oppositeLeviProjection F q) x
      rw [twoBlockDeformedBlocks_zero, twoBlockSecondDeformedBlocks_zero]))

/-- Every second-block coefficient at `u` comes from a first-block coefficient at `-u`
multiplied by `|det g|^u`: transport of the functional and vector along
`twistComparison`. -/
theorem exists_second_coefficient [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
    (ψ : UnitaryAdditiveCharacter F)
    (σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F) (W i)) (u : ℂ)
    (ℓ : glFunctionals ψ t (twoBlockDeformedInduced F m h σ (-u)))
    (hℓ : ℓ.val ≠ 0) (v) :
    ∃ ℓ' : glFunctionals ψ t (twoBlockSecondDeformedInduced F m h σ u), ℓ'.val ≠ 0 ∧
      ∃ v', ∀ g, ((⟨⟩ : LocalFieldData F).determinantComplexPower (t + 1) u g : ℂ) *
          ℓ.val (twoBlockDeformedInduced F m h σ (-u) g v) =
        ℓ'.val (twoBlockSecondDeformedInduced F m h σ u g v') := by
  let E := twistComparison F m h σ u
  let ℓ2 := twistFunctional (upperUnipotent (t + 1) F) (standardCharacter ψ t)
    ((⟨⟩ : LocalFieldData F).determinantComplexPower (t + 1) u)
    (determinantComplexPower_upperUnipotent F (t + 1) u) _ ℓ
  refine ⟨Whittaker.functionalsCongr E ℓ2, functionalsCongr_val_ne_zero E ℓ2 hℓ, E v,
    fun g => ?_⟩
  rw [functionalsCongr_val_rep]
  change _ = ℓ.val (((⟨⟩ : LocalFieldData F).determinantComplexPower (t + 1) u g : ℂ) •
    twoBlockDeformedInduced F m h σ (-u) g v)
  rw [map_smul, smul_eq_mul]

/-- The second clause at `u`, from the first-block clause at `-u` for the inverse
character of `ψ.scale (-1)`. -/
theorem secondCoefficient_of_firstCoefficient [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
    (ψ : UnitaryAdditiveCharacter F)
    (σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F) (W i))
    (V : ℂ → GeneralLinear (t + 1) F → ℂ) (u : ℂ)
    (hV : letI := isTopologicalRing F
      ∃ ℓ : glInverseFunctionals (ψ.scale (-1)) t (twoBlockDeformedInduced F m h σ (-u)),
        ℓ.val ≠ 0 ∧ ∃ v, ∀ g, V (-u) g = ℓ.val (twoBlockDeformedInduced F m h σ (-u) g v)) :
    ∃ ℓ : glFunctionals ψ t (twoBlockSecondDeformedInduced F m h σ u), ℓ.val ≠ 0 ∧
      ∃ v, ∀ g, ((⟨⟩ : LocalFieldData F).determinantComplexPower (t + 1) u g : ℂ) *
          V (-u) g = ℓ.val (twoBlockSecondDeformedInduced F m h σ u g v) := by
  let _ := isTopologicalRing F
  obtain ⟨ℓ', hℓ', v', hv'⟩ := hV
  obtain ⟨ℓ, hℓ, v, hv⟩ := exists_second_coefficient F m h ψ σ u
    (_root_.Langlands.RankinSelberg.functionalsCongr
      (inverseStandardCharacter_scale_neg_one ψ t) ℓ') hℓ' v'
  refine ⟨ℓ, hℓ, v, fun g => ?_⟩
  rw [hv' g]
  exact hv g

/-- Multiplying a family by `|det g|^u` and reversing the parameter keeps one common
compact open right stabilizer: intersect with the kernel of `|det|`. -/
theorem exists_level_twistedFamily [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
    (V : ℂ → GeneralLinear (t + 1) F → ℂ)
    (hV : ∃ K : Subgroup (GeneralLinear (t + 1) F),
        IsOpen (K : Set (GeneralLinear (t + 1) F)) ∧
        IsCompact (K : Set (GeneralLinear (t + 1) F)) ∧
        ∀ (u : ℂ) (g : GeneralLinear (t + 1) F) (k : K), V u (g * k) = V u g) :
    ∃ K : Subgroup (GeneralLinear (t + 1) F),
      IsOpen (K : Set (GeneralLinear (t + 1) F)) ∧
      IsCompact (K : Set (GeneralLinear (t + 1) F)) ∧
      ∀ (u : ℂ) (g : GeneralLinear (t + 1) F) (k : K),
        ((⟨⟩ : LocalFieldData F).determinantComplexPower (t + 1) u (g * k) : ℂ) *
            V (-u) (g * k) =
          ((⟨⟩ : LocalFieldData F).determinantComplexPower (t + 1) u g : ℂ) * V (-u) g := by
  have := (⟨⟩ : LocalFieldData F).generalLinearTopologicalGroup (t + 1)
  obtain ⟨K₀, hK₀o, hK₀c, hK₀⟩ := hV
  refine ⟨K₀ ⊓ ((⟨⟩ : LocalFieldData F).determinantNorm (t + 1)).ker, ?_, ?_, ?_⟩
  · exact hK₀o.inter ((⟨⟩ : LocalFieldData F).isOpen_ker_determinantNorm (t + 1))
  · exact hK₀c.inter_right (Subgroup.isClosed_of_isOpen _
      ((⟨⟩ : LocalFieldData F).isOpen_ker_determinantNorm (t + 1)))
  · intro u g k
    have hk : (⟨⟩ : LocalFieldData F).determinantNorm (t + 1)
        (k : GeneralLinear (t + 1) F) = 1 := k.property.2
    have hc : (⟨⟩ : LocalFieldData F).determinantComplexPower (t + 1) u
        (k : GeneralLinear (t + 1) F) = 1 := by
      apply Units.ext
      rw [Langlands.LocalFieldData.determinantComplexPower_apply, hk]
      simp
    rw [map_mul, Units.val_mul, hc, Units.val_one, mul_one,
      show V (-u) (g * k) = V (-u) g from hK₀ (-u) g ⟨k, k.property.1⟩]

/-- Multiplying a pointwise entire family by `|det g|^u` and reversing the parameter
keeps it pointwise entire. -/
theorem analyticAt_twistedFamily [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] (V : ℂ → GeneralLinear (t + 1) F → ℂ)
    (hV : ∀ (g : GeneralLinear (t + 1) F) (u : ℂ), AnalyticAt ℂ (fun z => V z g) u)
    (g : GeneralLinear (t + 1) F) (u : ℂ) :
    AnalyticAt ℂ (fun z =>
      ((⟨⟩ : LocalFieldData F).determinantComplexPower (t + 1) z g : ℂ) * V (-z) g) u := by
  have hpos : (0 : ℝ) <
      (((⟨⟩ : LocalFieldData F).determinantNorm (t + 1) g : NNReal) : ℝ) :=
    NNReal.coe_pos.2 (pos_iff_ne_zero.2
      ((⟨⟩ : LocalFieldData F).determinantNorm (t + 1) g).ne_zero)
  have hpow : AnalyticAt ℂ (fun z : ℂ =>
      ((⟨⟩ : LocalFieldData F).determinantComplexPower (t + 1) z g : ℂ)) u := by
    simp_rw [Langlands.LocalFieldData.determinantComplexPower_apply]
    exact AnalyticAt.cpow analyticAt_const analyticAt_id (Complex.ofReal_mem_slitPlane.2 hpos)
  have hneg : AnalyticAt ℂ (fun z : ℂ => V (-z) g) u :=
    (hV g (-u)).comp_of_eq analyticAt_id.neg rfl
  exact hpow.mul hneg

end TwoBlockSecondDeformation

open Langlands.RankinSelberg.TwoBlockSecondDeformation hiding ambientCharacter ambient_mul_firstBlock_eq_secondBlock analyticAt_twistedFamily determinantComplexPower_oppositeParabolic exists_level_twistedFamily exists_second_coefficient secondCoefficient_of_firstCoefficient twistComparison zeroComparison in
open Langlands.AllField.RankinSelberg.TwoBlockSecondDeformation in
/-- Entire standard-character deformation on the second lower-induced block, derived
from the published first-block inverse-character theorem by character change,
the parameter `-u` and the global twist `|det|^u`. -/
theorem twoBlockSecondWhittakerDeformation :
    TwoBlockSecondWhittakerDeformationStatement.{uF, uW} := by
  intro F _ _ _ _ ψ t m h W _ _ σ hσ ℓ₀ hℓ₀ v₀
  let _ := isTopologicalRing F
  have hη : ∀ i, IsOfWhittakerType (m i) (standardCharacter (ψ.scale (-1)) (m i)) (σ i) := by
    intro i
    rw [standardCharacter_scale_neg_one]
    exact (isOfWhittakerType_standard_iff_inverse ψ (σ i)).1 (hσ i)
  let E0 := zeroComparison F m h σ
  let ℓs : glInverseFunctionals (ψ.scale (-1)) t (twoBlockDeformedInduced F m h σ 0) :=
    _root_.Langlands.RankinSelberg.functionalsCongr
      (inverseStandardCharacter_scale_neg_one ψ t).symm
      ((Whittaker.functionalsCongr E0).symm ℓ₀)
  obtain ⟨V, hV0, hVu, hVK, hVa⟩ :=
    twoBlockWhittakerDeformation F (ψ.scale (-1)) t m h σ hη ℓs
      (functionalsCongr_symm_val_ne_zero E0 ℓ₀ hℓ₀) (E0.symm v₀)
  refine ⟨fun u g =>
    ((⟨⟩ : LocalFieldData F).determinantComplexPower (t + 1) u g : ℂ) * V (-u) g,
    fun g => ?_, fun u => ?_, exists_level_twistedFamily F V hVK,
    analyticAt_twistedFamily F V hVa⟩
  · have h1 : ((⟨⟩ : LocalFieldData F).determinantComplexPower (t + 1) 0 g : ℂ) = 1 := by
      rw [Langlands.LocalFieldData.determinantComplexPower_zero, MonoidHom.one_apply,
        Units.val_one]
    change ((⟨⟩ : LocalFieldData F).determinantComplexPower (t + 1) 0 g : ℂ) * V (-0) g = _
    rw [h1, neg_zero, one_mul (V 0 g), hV0 g]
    exact functionalsCongr_symm_val_rep E0 ℓ₀ g v₀
  · exact secondCoefficient_of_firstCoefficient F m h ψ σ V u (hVu (-u))

end Langlands.AllField.RankinSelberg
