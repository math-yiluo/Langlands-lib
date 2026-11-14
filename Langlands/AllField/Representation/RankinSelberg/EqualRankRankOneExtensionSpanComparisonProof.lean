import Langlands.Representation.RankinSelberg.EqualRankRankOneExtensionSpanComparisonProof
import Langlands.AllField.HarmonicAnalysis.PadicRowFourierSurjectivityProof
import Langlands.AllField.Representation.RankinSelberg.EqualRankLastRowReductionProof
import Langlands.AllField.Representation.RankinSelberg.EqualRankRankOneExtensionSpanComparisonStatement
import Langlands.AllField.Representation.RankinSelberg.RankOneExtensionSpanTransfer
import Langlands.AllField.Representation.RankinSelberg.ZeroRowLastRowCutoffProofSupplement
import Langlands.AllField.Representation.Whittaker.CoefficientRightStabilizer
import Langlands.AllField.Representation.Whittaker.TwoBlockExtensionAssemblyProof
/-!
# Equal-rank rank-one extension Laurent-span comparison: proof
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement EqualRankLastRowReductionStatement EqualRankRankOneExtensionSpanComparisonStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement LastRowCompactOrbitStatement QuotientHaarExistenceStatement RankOneExtensionLDivisibilityStatement RankOneExtensionSpanComparisonStatement RankOneWhittakerTypeStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement ZeroRowLastRowCutoffStatement equalRankLastRowReduction equalRankRankOneExtensionSpanComparison equalRankRankOneExtensionSpanComparison_of equalRankRankOneExtensionSpanComparison_of_rowFourierSurjectivity equalRankSpanComparison_core exists_inverseWhittaker_twoBlockExtension half_mul_determinantWeight isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt lastRowCompactOrbit normalizedAbsoluteValue normalizedAbsoluteValue_apply rankOneCharacter_isOfWhittakerType rankOneExtensionCharacter rankOneExtensionCharacter_isOfWhittakerType rankOneExtensionCharacter_isSmooth rankOneExtensionLowerFamily rankOneExtensionLowerInduced rankOneExtensionLowerModel rankOneExtensionLowerSection rankOneExtensionLowerSectionCoefficient rankOneExtensionLowerSectionEval rankOneExtensionLowerToUpperEquiv rankOneExtensionSpanComparison_of_pointwise rankOneExtensionWhittakerContraction rankOneWhittakerType zeroRowLastRowCutoff
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory
open Langlands.HarmonicAnalysis hiding PadicMatrixFourierSliceStatement PadicRowFourierSurjectivityStatement PadicSelfDualMeasureExistsStatement padicLatticeGeometry padicMatrixFourierSlice padicRectangularHaarScaling padicRowFourierSurjectivity padicScalarHaarScaling padicSelfDualMeasureExists
open Langlands.AllField.HarmonicAnalysis
open Langlands.Whittaker hiding TwoBlockCellCoefficientStatement TwoBlockCellJacquetIntegrabilityStatement TwoBlockCellSectionStatement TwoBlockCellUnipotentStabilityStatement TwoBlockExtensionAssemblyStatement TwoBlockInducedCarrier TwoBlockInducingWhittakerCovarianceStatement TwoBlockJacquetCovarianceStatement TwoBlockJacquetFunctionalExtensionStatement TwoBlockLeadingTranslationStatement TwoBlockWhittakerExtensionStatement exchangedParabolic exists_compactOpen_glCoefficientRightStabilizer exists_openSubgroup_subset_parabolic_mul_opposite functionalsCongr hasCompactSupport_twoBlockCellRestriction mul_upperUnipotent_mem_twoBlockCell oppositeLower swapRank_exchangedParabolic twoBlockCell twoBlockCellCoefficient twoBlockCellInclusion twoBlockCellInclusion_apply twoBlockCellJacquetIntegrability twoBlockCellPoint twoBlockCellPoint_mul_upperUnipotent twoBlockCellRestriction twoBlockCellSection twoBlockCellSubmodule twoBlockCellUnipotentStability twoBlockEval twoBlockHalfModulus_mul_detPow twoBlockInduced twoBlockInducingRepresentation twoBlockInducingWhittakerCovariance twoBlockJacquetCovariance twoBlockJacquetFunctionalExtension twoBlockLeadingTranslation twoBlockParabolic twoBlockRestriction twoBlockWhittakerExtension_of_rowFourierSurjectivity unipotentLeviFactor unipotentShift
open Langlands.AllField.Whittaker
open Langlands.GeneralLinear hiding upperUnipotentCompactContainment upperUnipotent_isLimitOfCompactSubgroups
open Langlands.AllField.GeneralLinear
open Langlands.QuotientIntegration

universe uF uV uW uV' uU

section CharacterChange


end CharacterChange

section Restriction


end Restriction

section Convergence


end Convergence

section Weight

variable {F : Type uF} [Field F] (T : LocalFieldData F)

/-- The half power of the determinant combines with the corank-one weight. -/
theorem half_mul_determinantWeight {n : ℕ} (g : Langlands.GeneralLinear (n + 1) F)
    (s : ℂ) :
    (Real.rpow (T.normalizedAbs (Matrix.det g.val)) ((1 : ℝ) / 2) : ℂ) *
        determinantWeight (normalizedAbsoluteValue T) g (s - 1 / 2 - 1 / 2) =
      determinantWeight (normalizedAbsoluteValue T) g (s - 1 / 2) := by
  have hdet : Matrix.det g.val ≠ 0 := g.isUnit.map Matrix.detMonoidHom |>.ne_zero
  have hpos : 0 < T.normalizedAbs (Matrix.det g.val) := by
    rcases (T.normalizedAbs_nonneg (Matrix.det g.val)).lt_or_eq with h | h
    · exact h
    · exact absurd ((T.normalizedAbs_eq_zero_iff _).1 h.symm) hdet
  set a := T.normalizedAbs (Matrix.det g.val) with ha
  have ha0 : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hpos.ne'
  unfold determinantWeight
  change ((a ^ ((1 : ℝ) / 2) : ℝ) : ℂ) * (a : ℂ) ^ (s - 1 / 2 - 1 / 2) = (a : ℂ) ^ (s - 1 / 2)
  rw [Complex.ofReal_cpow hpos.le, ← Complex.cpow_add _ _ ha0]
  congr 1
  push_cast
  ring

end Weight

section Transport

end Transport

section Extension


/-- JPSS Proposition 9.1 with a rank-one first block, read in the
inverse-character model of the induction of the unlifted pair `(χ, σ₁)`. -/
theorem exists_inverseWhittaker_twoBlockExtension
    (h91 : Langlands.AllField.Whittaker.TwoBlockWhittakerExtensionStatement.{uF, 0, uW})
    (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
    (ψ : UnitaryAdditiveCharacter F)
    (t : ℕ) {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (σ₁ : Representation ℂ (Langlands.GeneralLinear (t + 1) F) W)
    (χ : Quasicharacter F)
    (hσ : IsOfWhittakerType t (standardCharacter ψ t) σ₁) :
    ∀ W₁ ∈ inverseWhittakerSet ψ t σ₁, ∀ Φ₀ : SchwartzBruhat (Fin (t + 1) → F),
      ∃ W' ∈ inverseWhittakerSet ψ (1 + t) ((⟨⟩ : LocalFieldData F).normalizedProductInduced
          (Shahidi.twoBlocks 1 (t + 1) (Nat.succ_pos 0) (Nat.succ_pos t))
          (Shahidi.pairFamily
            ((ULift.moduleEquiv.symm.conjRingEquiv.toMonoidHom).comp
              (rankOneCharacter (χ : Fˣ →* ℂˣ)) :
                Representation ℂ (Langlands.GeneralLinear 1 F) (ULift.{uW} ℂ))
            σ₁)),
        ∀ g : Langlands.GeneralLinear (t + 1) F,
          W'.val (GeneralLinear.reindex (finCongr (by omega : t + 1 + 1 = 1 + t + 1))
              (rankInclusion 1 g)) =
            W₁.val g * Φ₀ (lastRow g) *
              (Real.rpow ((⟨⟩ : LocalFieldData F).normalizedAbs (Matrix.det g.val))
                ((1 : ℝ) / 2) : ℂ) := by
  intro W₁ hW₁ Φ₀
  have hσ' : IsOfWhittakerType t (standardCharacter (ψ.scale (-1)) t) σ₁ := by
    rw [standardCharacter_scale_neg_one]
    exact (isOfWhittakerType_standard_iff_inverse ψ σ₁).1 hσ
  have hχ := rankOneCharacter_isOfWhittakerType F (ψ.scale (-1)) χ
  obtain ⟨W₂, hW₂, hW₂val⟩ := exists_whittakerSet_scale_neg_one ψ hW₁
  obtain ⟨Wξ, hWξ, hWξval⟩ := h91 F (ψ.scale (-1)) 0 t
    (rankOneCharacter (χ : Fˣ →* ℂˣ)) σ₁ hχ hσ' W₂ hW₂ Φ₀
  obtain ⟨W', hW', hW'val⟩ := exists_inverseWhittakerSet_of_scale_neg_one ψ hWξ
  refine ⟨W', (Set.ext_iff.1 (inverseWhittakerSet_eq_of_equiv ψ
    ((⟨⟩ : LocalFieldData F).normalizedProductInducedEquiv
      (Shahidi.twoBlocks 1 (t + 1) (Nat.succ_pos 0) (Nat.succ_pos t))
      (pairFamilyEquivRight _ (conjULiftEquiv.{uW, 0} σ₁)))) W').2 hW', fun g => ?_⟩
  refine (congrFun hW'val _).trans ((hWξval g).trans ?_)
  rw [hW₂val]
  norm_num

end Extension

section Core


/-- The span comparison at a general induced rank `m = t + 1`, from the
last-row reduction, the zero-row cutoff and a supplied extension of inverse
Whittaker functions of `σ₁` to inverse Whittaker functions of `I`. -/
theorem equalRankSpanComparison_core (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
    (ψ : UnitaryAdditiveCharacter F)
    (ν : letI := borel F
      AdditiveHaarMeasure F)
    (t m : ℕ) (hm : t + 1 = m)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    {U : Type uU} [AddCommGroup U] [Module ℂ U]
    (π : Representation ℂ (Langlands.GeneralLinear (t + 2) F) V)
    (σ₁ : Representation ℂ (Langlands.GeneralLinear (t + 1) F) W)
    (I : Representation ℂ (Langlands.GeneralLinear (m + 1) F) U)
    (hC : EqualRankLastRowReductionStatement F (⟨⟩ : LocalFieldData F) t)
    (hπ : IsSmooth π)
    (hI : IsSmooth I)
    (hext : ∀ W₁ ∈ inverseWhittakerSet ψ t σ₁, ∀ Φ₀ : SchwartzBruhat (Fin (t + 1) → F),
        ∃ W' ∈ inverseWhittakerSet ψ m I, ∀ g : Langlands.GeneralLinear (t + 1) F,
          W'.val (GeneralLinear.reindex (finCongr (by omega : t + 1 + 1 = m + 1))
              (rankInclusion 1 g)) =
            W₁.val g * Φ₀ (lastRow g) *
              (Real.rpow ((⟨⟩ : LocalFieldData F).normalizedAbs (Matrix.det g.val))
                ((1 : ℝ) / 2) : ℂ)) :
    letI := borel F
    letI : BorelSpace F := ⟨rfl⟩
    letI := borel (Langlands.GeneralLinear (t + 1) F)
    letI : BorelSpace (Langlands.GeneralLinear (t + 1) F) := ⟨rfl⟩
    letI := borel (upperUnipotent (t + 1) F)
    letI : BorelSpace (upperUnipotent (t + 1) F) := ⟨rfl⟩
    letI := borel (LeftUnipotentQuotient t F)
    letI := borel (Langlands.GeneralLinear (m + 1) F)
    letI : BorelSpace (Langlands.GeneralLinear (m + 1) F) := ⟨rfl⟩
    letI := borel (upperUnipotent (m + 1) F)
    letI : BorelSpace (upperUnipotent (m + 1) F) := ⟨rfl⟩
    letI := borel (LeftUnipotentQuotient m F)
    ∀ [Measure.IsMulRightInvariant (unipotentHaar F t)],
    ∀ [Measure.IsMulRightInvariant (unipotentHaar F m)],
    ∀ (μbase : Measure (LeftUnipotentQuotient t F))
      (μind : Measure (LeftUnipotentQuotient m F)),
      IsCompatible (upperUnipotent (t + 1) F)
        (generalLinearHaar F t) (unipotentHaar F t) μbase →
      IsCompatible (upperUnipotent (m + 1) F)
        (generalLinearHaar F m) (unipotentHaar F m) μind →
        zetaSpan (unequalRankZetaValuesAt (r := t + 1) (n := t) 0 0 rfl
          (⟨⟩ : LocalFieldData F).residueCardinality ψ
          (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) μbase
          (rectangularMeasure ν 0 (t + 1)) π σ₁) ≤
        zetaSpan (equalRankZetaValues (n := m)
          (⟨⟩ : LocalFieldData F).residueCardinality ψ
          (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) μind
          (hm ▸ π : Representation ℂ (Langlands.GeneralLinear (m + 1) F) V) I) := by
  subst hm
  let := borel F
  have : BorelSpace F := ⟨rfl⟩
  let := borel (Langlands.GeneralLinear (t + 1) F)
  have : BorelSpace (Langlands.GeneralLinear (t + 1) F) := ⟨rfl⟩
  let := borel (upperUnipotent (t + 1) F)
  have : BorelSpace (upperUnipotent (t + 1) F) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient t F)
  let := borel (Langlands.GeneralLinear (t + 1 + 1) F)
  have : BorelSpace (Langlands.GeneralLinear (t + 1 + 1) F) := ⟨rfl⟩
  let := borel (upperUnipotent (t + 1 + 1) F)
  have : BorelSpace (upperUnipotent (t + 1 + 1) F) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient (t + 1) F)
  intro _ _ μbase μind hbase hind
  refine zetaSpan_le_of_forall_exists_const_mul fun R hR => ?_
  obtain ⟨Wπ, ⟨ℓ, hℓ⟩, W₁, hW₁, ⟨a, ha⟩, hRc⟩ := hR
  obtain ⟨Φ₀, -, hcut⟩ := zeroRowLastRowCutoff F (⟨⟩ : LocalFieldData F) t 0 ψ V π hπ ℓ
    ⟨Wπ, hℓ⟩
  obtain ⟨W', ⟨ℓ', hℓ'⟩, hW'val⟩ := hext W₁ hW₁ Φ₀
  simp only [reindex_finCongr_self] at hW'val
  obtain ⟨J, hJ, ⟨hJW, hJW'⟩, -⟩ := Langlands.AllField.Whittaker.exists_compactOpen_glCoefficientRightStabilizer
    F (⟨⟩ : LocalFieldData F) (t + 1) ψ V U π I hπ hI ℓ ℓ' ⟨Wπ, hℓ⟩ ⟨W', hℓ'⟩
  obtain ⟨-, -, -, -, ⟨Φ, hΦ⟩, -⟩ := lastRowCompactOrbit F (⟨⟩ : LocalFieldData F) (t + 1) J hJ
  obtain ⟨c, hc, hcW⟩ := hC μind μbase hind hbase J hJ
  have hint : ∀ s : ℂ, corankOneIntegrand (n := t) ψ
      (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) Wπ (corankOneRestrict ψ W')
        (s - 1 / 2) =
      corankOneIntegrand (n := t) ψ (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F))
        Wπ W₁ s := by
    intro s
    funext q
    induction q using Quotient.inductionOn with
    | h g =>
      rw [corankOneIntegrand_mk, corankOneIntegrand_mk, corankOneRestrict_val, hW'val g,
        ← half_mul_determinantWeight (⟨⟩ : LocalFieldData F) g s]
      have hg : Wπ.val (rankInclusion 1 g) * Φ₀ (lastRow g) = Wπ.val (rankInclusion 1 g) :=
        hcut g
      calc _ = (Wπ.val (rankInclusion 1 g) * Φ₀ (lastRow g)) * W₁.val g *
            ((Real.rpow ((⟨⟩ : LocalFieldData F).normalizedAbs (Matrix.det g.val))
                ((1 : ℝ) / 2) : ℂ) *
              determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) g
                (s - 1 / 2 - 1 / 2)) := by ring
        _ = _ := by rw [hg]
  have hred := fun s => hcW ψ Wπ W' (corankOneRestrict ψ W') Φ hJW hJW' (fun _ => rfl) hΦ s
  refine ⟨(c : ℂ), Complex.ofReal_ne_zero.2 hc.ne', ?_⟩
  refine ⟨Wπ, ⟨ℓ, hℓ⟩, W', ⟨ℓ', hℓ'⟩, Φ, ⟨a, fun s hs => ?_⟩, ?_⟩
  · have h1 := ha s hs
    rw [rectangularMeasure_zero_rows] at h1
    have h2 := corankOneConverges_of_unequalRankConverges_zero_zero ψ _ μbase Wπ W₁ s h1
    refine (hred s).1.2 ?_
    unfold CorankOneConverges
    rw [hint s]
    exact h2
  · have heq : equalRankIntegral ψ (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) μind
        Wπ W' Φ = fun s => (c : ℂ) * corankOneIntegral ψ
          (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) μbase Wπ W₁ s := by
      funext s
      rw [(hred s).2]
      unfold corankOneIntegral
      rw [hint s]
    have hzero : unequalRankIntegral ψ (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F))
        0 0 μbase (Measure.dirac 0) Wπ W₁ =
        corankOneIntegral ψ (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) μbase Wπ W₁ :=
      funext fun s => unequalRankIntegral_zero_zero ψ _ μbase Wπ W₁ s
    rw [heq]
    apply hasRationalContinuation_const_mul
    rw [rectangularMeasure_zero_rows, hzero] at hRc
    exact hRc

end Core

/-- The span comparison from JPSS Proposition 9.1 and the last-row reduction
`equalRankLastRowReduction`. -/
theorem equalRankRankOneExtensionSpanComparison_of
    (h91 : Langlands.AllField.Whittaker.TwoBlockWhittakerExtensionStatement.{uF, 0, uW}) :
    EqualRankRankOneExtensionSpanComparisonStatement.{uF, uV, uW} := by
  intro F _ _ _ _ ψ ν t V _ _ W _ _ π σ₁ χ hπ hσ χlift
  intro _ _ μbase μind hbase hind hrn
  exact equalRankSpanComparison_core F ψ ν t (1 + t) hrn π σ₁
    ((⟨⟩ : LocalFieldData F).normalizedProductInduced
      (Shahidi.twoBlocks 1 (t + 1) (Nat.succ_pos 0) (Nat.succ_pos t))
      (Shahidi.pairFamily χlift σ₁))
    (equalRankLastRowReduction F (⟨⟩ : LocalFieldData F) t) hπ.1.1
    ((⟨⟩ : LocalFieldData F).isSmooth_normalizedProductInduced _ _)
    (exists_inverseWhittaker_twoBlockExtension h91 F ψ t σ₁ χ hσ) μbase μind hbase hind

/-- The span comparison from p-adic row Fourier surjectivity, through the
published conditional proof `Langlands.AllField.Whittaker.twoBlockWhittakerExtension_of_rowFourierSurjectivity`
of JPSS Proposition 9.1. -/
theorem equalRankRankOneExtensionSpanComparison_of_rowFourierSurjectivity
    (hsurj : ∀ (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] (d : ℕ),
      Langlands.AllField.HarmonicAnalysis.PadicRowFourierSurjectivityStatement F (⟨⟩ : LocalFieldData F) d) :
    EqualRankRankOneExtensionSpanComparisonStatement.{uF, uV, uW} :=
  equalRankRankOneExtensionSpanComparison_of
    (Langlands.AllField.Whittaker.twoBlockWhittakerExtension_of_rowFourierSurjectivity.{uF, 0, uW} hsurj)

/-- The equal-rank rank-one extension Laurent-span comparison, from the
published proof `Langlands.AllField.HarmonicAnalysis.padicRowFourierSurjectivity`. -/
theorem equalRankRankOneExtensionSpanComparison :
    EqualRankRankOneExtensionSpanComparisonStatement.{uF, uV, uW} :=
  equalRankRankOneExtensionSpanComparison_of_rowFourierSurjectivity
    (fun F _ _ _ _ d =>
      Langlands.AllField.HarmonicAnalysis.padicRowFourierSurjectivity F (⟨⟩ : LocalFieldData F) d)

end Langlands.AllField.RankinSelberg
