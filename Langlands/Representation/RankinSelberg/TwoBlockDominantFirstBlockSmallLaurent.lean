import Langlands.Representation.RankinSelberg.TwoBlockDominantFirstBlockDisintegration
import Langlands.Representation.RankinSelberg.TwoBlockSmallFunctionalEquationLaurentBridge

/-! # The actual smaller Laurent identity on dominant first-block fibers -/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.RankinSelberg.TwoBlockDominantFirstBlock

open MeasureTheory GeneralLinear Whittaker HarmonicAnalysis TwoBlockJacquet
  TwoBlockFirstBlockQuotient TwoBlockLowerUnipotentQuotient
  TwoBlockLowerFirstBlockQuotient TwoBlockFirstBlockLaurent QuotientIntegration
  HarmonicAnalysis.BilateralLaurentSeries

universe uF uV uW

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance smallLaurentTopology : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance smallLaurentValuation : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
local instance smallLaurentLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance smallLaurentT2 : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance smallLaurentCountable : SecondCountableTopology F.Carrier :=
  F.canonicalTopologicalData.secondCountableTopology
local instance smallLaurentGLTopology (a : ℕ) : IsTopologicalGroup (GeneralLinear a F.Carrier) :=
  F.canonicalTopologicalData.generalLinearTopologicalGroup a
local instance smallLaurentGLCountable (a : ℕ) : SecondCountableTopology (GeneralLinear a F.Carrier) :=
  F.canonicalTopologicalData.generalLinearSecondCountableTopology a
local instance smallLaurentMeasurable : MeasurableSpace F.Carrier := borel _
local instance smallLaurentBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance smallLaurentGLMeasurable (a : ℕ) : MeasurableSpace (GeneralLinear a F.Carrier) := borel _
local instance smallLaurentGLBorel (a : ℕ) : BorelSpace (GeneralLinear a F.Carrier) := ⟨rfl⟩
local instance smallLaurentNMeasurable (a : ℕ) :
    MeasurableSpace (upperUnipotent a F.Carrier) := borel _
local instance smallLaurentNBorel (a : ℕ) : BorelSpace (upperUnipotent a F.Carrier) := ⟨rfl⟩
local instance smallLaurentNCountable (a : ℕ) :
    SecondCountableTopology (upperUnipotent a F.Carrier) :=
  Topology.IsEmbedding.subtypeVal.secondCountableTopology
local instance smallLaurentNQMeasurable (a : ℕ) :
    MeasurableSpace (LeftUnipotentQuotient a F.Carrier) := borel _
local instance smallLaurentNQBorel (a : ℕ) :
    BorelSpace (LeftUnipotentQuotient a F.Carrier) := ⟨rfl⟩


variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1) (j k : ℕ)
variable {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
variable {σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F.Carrier) (W i)}
variable {ψ : UnitaryAdditiveCharacter F.Carrier}
variable (ell : ∀ i, glInverseFunctionals ψ (m i) (σ i)) (f : Sections F h σ)
variable (Wtest : WhittakerFunctions ψ (t + (j + k + 1)))
variable (ν : AdditiveHaarMeasure F.Carrier)

include h in
/-- The smaller test rank is strictly greater than the first-block rank. -/
theorem firstBlockSmallRank_lt : m 0 < t + (j + k + 1) := by
  have := blockRanks_add h
  omega

/-- The reflected, transformed smaller JPSS slice coefficient, with the same
base determinant factor as the actual upper first-block coefficient. -/
def firstBlockReflectedSmallCoefficient
    (μ : Measure (LeftUnipotentQuotient (m 0) F.Carrier)) (d : ℤ)
    (Y : Matrix (Fin j) (Fin (m 1 + 1)) F.Carrier)
    (g : GeneralLinear (t + 1) F.Carrier) : ℂ :=
  determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData) g
      (0 - ((j + k + 1 : ℕ) : ℂ) / 2 + (j : ℂ)) *
    reflectSeries F.canonicalTopologicalData.residueCardinality
      (fun n => unequalRankSliceCoefficientAt F k (m 1 + 1 + j)
        (by have := firstBlockSmallRank h j k; omega) (ψ.scale (-1)) μ
        (rectangularMeasure ν k (m 0 + 1))
        (translateWhittaker (ψ.scale (-1)) (t + (j + k + 1))
          (firstDualFunction ψ (t + (j + k + 1))
            (translateWhittaker ψ (t + (j + k + 1)) Wtest
              (rectangularUnipotent j k (firstBlockColumns h j 0 Y) *
                appendIdentity t (j + k + 1) g)))
          (blockWeylAt (m 0) (t + (j + k + 1)) (firstBlockSmallRank_lt h j k)))
        (secondDualFunction ψ (m 0) (firstBlockCoefficient ell f g).val) n) d

/-- The actual small functional equation gives the finite Laurent identity
at every remaining-column matrix and base representative. Both normalized
generators are retained, and no bilateral polynomial is cancelled. -/
theorem firstBlock_small_laurent_identity
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GeneralLinear (t + (j + k + 1) + 1) F.Carrier) V)
    (lambda : glFunctionals ψ (t + (j + k + 1)) π)
    (hπ : IsOfWhittakerType (t + (j + k + 1))
      (standardCharacter ψ (t + (j + k + 1))) π)
    (hσ : IsOfWhittakerType (m 0) (inverseStandardCharacter ψ (m 0)) (σ 0))
    (Wmodel : (coefficientModel π lambda).toSubmodule)
    [Measure.IsMulRightInvariant (unipotentHaar F.Carrier (m 0))]
    (μ : Measure (LeftUnipotentQuotient (m 0) F.Carrier)) [SigmaFinite μ]
    (hμ : IsCompatible (upperUnipotent (m 0 + 1) F.Carrier)
      (generalLinearHaar F.Carrier (m 0)) (unipotentHaar F.Carrier (m 0)) μ)
    (ζ cε : ℂˣ) (e : ℤ) (P Pdual : Polynomial ℂ)
    (hP : IsNormalizedGenerator
      (unequalRankValuesAt (m 1 + 1 + j) k (firstBlockSmallRank h j k)
        F.canonicalTopologicalData.residueCardinality ψ
        (normalizedAbsoluteValue F.canonicalTopologicalData) μ
        (rectangularMeasure ν (m 1 + 1 + j) (m 0 + 1)) π (σ 0) lambda (ell 0)) P)
    (hPd : IsNormalizedGenerator
      (dualUnequalRankRationalValuesAt (firstBlockSmallRank_lt h j k)
        (m 1 + 1 + j) k (firstBlockSmallRank h j k)
        F.canonicalTopologicalData.residueCardinality ψ
        (normalizedAbsoluteValue F.canonicalTopologicalData) μ ν π (σ 0) lambda (ell 0)) Pdual)
    (hpairs : ∀ (fs : (coefficientModel π lambda).toSubmodule)
      (ff : (coefficientModel (σ 0) (ell 0)).toSubmodule),
      ∃ R Rdual : RationalFunctions,
        HasRationalContinuation F.canonicalTopologicalData.residueCardinality
          (unequalRankIntegralAt (m 1 + 1 + j) k (firstBlockSmallRank h j k) ψ
            (normalizedAbsoluteValue F.canonicalTopologicalData) μ
            (rectangularMeasure ν (m 1 + 1 + j) (m 0 + 1)) fs.val ff.val) R ∧
        HasRationalContinuation F.canonicalTopologicalData.residueCardinality
          (dualUnequalRankModelIntegralAt (firstBlockSmallRank_lt h j k)
            (m 1 + 1 + j) k (firstBlockSmallRank h j k) ψ
            (normalizedAbsoluteValue F.canonicalTopologicalData) μ ν π (σ 0)
            lambda (ell 0) fs ff) Rdual ∧
        NormalizedFunctionalEquation F.canonicalTopologicalData.residueCardinality
          P Pdual ζ cε (t + (j + k + 1)) e R Rdual)
    (Y : Matrix (Fin j) (Fin (m 1 + 1)) F.Carrier)
    (g : GeneralLinear (t + 1) F.Carrier) :
    let Zlow : BilateralLaurentSeries :=
      fun d => firstBlockReflectedSmallCoefficient F h j k ell f Wmodel.val ν μ d Y g
    let Zup : BilateralLaurentSeries :=
      fun d => firstBlockUpperCoefficient F h j k ell f Wmodel.val ν μ d Y g
    reflectedPolynomial F.canonicalTopologicalData.residueCardinality Pdual • Zlow =
      (LaurentPolynomial.C ((ζ : ℂ) ^ (t + (j + k + 1)) * (cε : ℂ)) *
          LaurentPolynomial.T e * P.toLaurent) •
        Zup := by
  dsimp only
  obtain ⟨hlam, hell⟩ := normalizedGenerator_functionals_ne_zero
    F.canonicalTopologicalData.residueCardinality_gt_one
    (m 1 + 1 + j) k (firstBlockSmallRank h j k) hP
  let fs := translateModelEquiv ψ π lambda
    (rectangularUnipotent j k (firstBlockColumns h j 0 Y) *
      appendIdentity t (j + k + 1) g) Wmodel
  let ff := firstBlockCoefficient ell f g
  obtain ⟨R, Rd, hR, hRd, hFE⟩ := hpairs fs ff
  have hRm : R ∈ unequalRankValuesAt (m 1 + 1 + j) k (firstBlockSmallRank h j k)
      F.canonicalTopologicalData.residueCardinality ψ
      (normalizedAbsoluteValue F.canonicalTopologicalData) μ
      (rectangularMeasure ν (m 1 + 1 + j) (m 0 + 1)) π (σ 0) lambda (ell 0) := by
    rw [unequalRankValuesAt_eq]
    exact ⟨fs, ff, hR⟩
  have hRdm : Rd ∈ dualUnequalRankRationalValuesAt (firstBlockSmallRank_lt h j k)
      (m 1 + 1 + j) k (firstBlockSmallRank h j k)
      F.canonicalTopologicalData.residueCardinality ψ
      (normalizedAbsoluteValue F.canonicalTopologicalData) μ ν π (σ 0) lambda (ell 0) :=
    ⟨fs, ff, hRd⟩
  have heq := smallFE_coefficient_identity F.canonicalTopologicalData.residueCardinality_gt_one
    hP hPd hRm hRdm hR hRd hFE
    (smallIntegral_series F (m 1 + 1 + j) k (firstBlockSmallRank h j k) ψ μ hμ
      inferInstance ν π (σ 0) hπ hσ lambda (ell 0) hlam hell fs ff)
    (dualSmallIntegral_series F (firstBlockSmallRank_lt h j k) (m 1 + 1 + j) k
      (firstBlockSmallRank h j k) ψ μ hμ inferInstance ν π (σ 0) hπ hσ
      lambda (ell 0) hlam hell fs ff)
  have hupper : (fun d => firstBlockUpperCoefficient F h j k ell f Wmodel.val ν μ d Y g) =
      determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData) g
        (0 - ((j + k + 1 : ℕ) : ℂ) / 2 + (j : ℂ)) •
      (fun d => unequalRankSliceCoefficientAt F (m 1 + 1 + j) k
        (firstBlockSmallRank h j k) ψ μ (rectangularMeasure ν (m 1 + 1 + j) (m 0 + 1))
        fs.val ff.val d) := by
    funext d
    exact (firstBlockUpperCoefficient_eq_small_of_whittakerType F h j k ell f ν
      π lambda hπ hσ Wmodel μ hμ d Y g).2
  rw [hupper]
  let c : ℂ := determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData) g
    (0 - ((j + k + 1 : ℕ) : ℂ) / 2 + (j : ℂ))
  change reflectedPolynomial _ Pdual • (c • reflectSeries _ _) =
    (LaurentPolynomial.C ((ζ : ℂ) ^ (t + (j + k + 1)) * (cε : ℂ)) *
      LaurentPolynomial.T e * P.toLaurent) • (c • _)
  rw [smul_comm (reflectedPolynomial _ Pdual) c,
    smul_comm (_ * _ * P.toLaurent) c]
  exact congrArg (fun Z : BilateralLaurentSeries => c • Z) heq

end Langlands.RankinSelberg.TwoBlockDominantFirstBlock
