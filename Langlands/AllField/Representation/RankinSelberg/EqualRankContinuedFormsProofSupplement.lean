import Langlands.Representation.RankinSelberg.EqualRankContinuedFormsProof
import Langlands.AllField.HarmonicAnalysis.PadicRowFourierEquivarianceProof
import Langlands.AllField.Representation.RankinSelberg.EqualRankCharacterChange
import Langlands.AllField.Representation.RankinSelberg.EqualRankContinuedFormsProof
import Langlands.AllField.Representation.RankinSelberg.EqualRankContinuedFormsStatement
/-!
# Construction of the continued normalized equal-rank trilinear forms

The cleared rational continuations of the original and Fourier-dual equal-rank
integrals have unique Laurent lifts, linear in the test triple. Evaluating them at
the nonzero spectral points `q^(-s)` and `q^(-(1-s))` gives trilinear forms for
every complex parameter. Their twisted invariance follows from the monomial
translation laws of the lifts, and they agree with the normalized rational
continuations wherever the relevant continuation is regular.
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankContinuedFormsStatement EqualRankFunctionalEquationStatement QuotientHaarExistenceStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement equalRankContinuedForms isEqualRankLPolynomial_characterChange_normalized normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedAbsoluteValue_det_eq_zpow normalizedDeterminantWeight_eq_spectralPoint_zpow padic_rowFourier_equivariance padic_row_instances padic_row_translate_exists zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory
open Langlands.HarmonicAnalysis hiding PadicRowFourierEquivarianceStatement padicRectangularHaarScaling padicRowFourierEquivariance padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis
open Langlands.Whittaker
open Langlands.GeneralLinear
open Langlands.QuotientIntegration

universe uF uV uW

section RowFourierMap


end RowFourierMap

section Determinant


end Determinant

section Spectral

end Spectral

section Padic

variable {F : Type uF} [Field F] (T : LocalFieldData F)

/-- The p-adic row Fourier equivariance, read in the instance context of the
continued-forms statement with the normalized absolute value. -/
theorem padic_rowFourier_equivariance (n : ℕ) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := IsTopologicalAddGroup.rightUniformSpace F
    letI := isUniformAddGroup_of_addCommGroup (G := F)
    letI := borel F
    letI : BorelSpace F := ⟨rfl⟩
    ∀ (ψ : UnitaryAdditiveCharacter F) (ν : AdditiveHaarMeasure F)
      (g : Langlands.GeneralLinear (n + 1) F)
      (Φ Φg : SchwartzBruhat (Fin (n + 1) → F)),
      (∀ x, Φg x = Φ (Matrix.vecMul x g.val)) → ∀ y,
        rowFourierIntegral ψ ν (n + 1) Φg y =
          ((normalizedAbsoluteValue T (Matrix.det g.val) : ℂ)⁻¹) *
            rowFourierIntegral ψ ν (n + 1) Φ (Matrix.vecMul y (Matrix.transpose (g⁻¹).val)) := by
  intro ψ ν g Φ Φg hΦg y
  exact (Langlands.AllField.HarmonicAnalysis.padicRowFourierEquivariance F T (n + 1) ψ ν g Φ).2 Φg hΦg y

/-- Right translates of row Schwartz--Bruhat functions exist, in the instance
context of the continued-forms statement (first half of the published
equivariance theorem). -/
theorem padic_row_translate_exists (n : ℕ) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := borel F
    letI : BorelSpace F := ⟨rfl⟩
    ∀ (_ψ : UnitaryAdditiveCharacter F) (_ν : AdditiveHaarMeasure F)
      (g : Langlands.GeneralLinear (n + 1) F)
      (Φ : SchwartzBruhat (Fin (n + 1) → F)),
      ∃ Φg : SchwartzBruhat (Fin (n + 1) → F), ∀ x, Φg x = Φ (Matrix.vecMul x g.val) := by
  intro ψ ν g Φ
  exact (Langlands.AllField.HarmonicAnalysis.padicRowFourierEquivariance F T (n + 1) ψ ν g Φ).1

end Padic

section LaurentSpectral

end LaurentSpectral

section Assembly



end Assembly

/-- **Continued normalized equal-rank trilinear forms.** Proof of
`EqualRankContinuedFormsStatement`. -/
theorem equalRankContinuedForms (F : Type uF) [Field F]
    (T : LocalFieldData F) (n : ℕ) : EqualRankContinuedFormsStatement.{uF, uV, uW} F T n := by
  have hequiv := padic_rowFourier_equivariance T n
  have htrans := padic_row_translate_exists T n
  have hinst := padic_row_instances T n
  unfold EqualRankContinuedFormsStatement
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := IsTopologicalAddGroup.rightUniformSpace F
  let := isUniformAddGroup_of_addCommGroup (G := F)
  let := borel F
  let : BorelSpace F := ⟨rfl⟩
  let := borel (Langlands.GeneralLinear (n + 1) F)
  let : BorelSpace (Langlands.GeneralLinear (n + 1) F) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1) F)
  let : BorelSpace (upperUnipotent (n + 1) F) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient n F)
  let : BorelSpace (LeftUnipotentQuotient n F) := ⟨rfl⟩
  intro ψ _ μ hμ ν V _ _ W _ _ π σ _ _ ℓ ℓ' _ _ q abv hA hAd hF P Pd hP hPd M M' S
    IsTwistedInvariant
  obtain ⟨hB, hS⟩ := hinst ν
  exact continuedForms_of_laws ψ μ hμ.right_invariant ν π σ ℓ ℓ' T.residueCardinality_gt_one
    abv (fun g => ⟨_, normalizedAbsoluteValue_det_eq_zpow T g⟩) (htrans ψ ν) (hequiv ψ ν)
    hA hAd hF P Pd hP hPd

end Langlands.AllField.RankinSelberg
