import Langlands.Representation.RankinSelberg.UnequalRankGammaPropagationProof
import Langlands.AllField.Representation.RankinSelberg.UnequalRankBlockSpanProof
import Langlands.AllField.Representation.RankinSelberg.UnequalRankBlockZeroGammaStatement
import Langlands.AllField.Representation.RankinSelberg.UnequalRankComplementaryTransferProof
import Langlands.AllField.Representation.RankinSelberg.UnequalRankGammaPropagationStatement
/-! Same-multiplier propagation from the published paired transfer and
adjacent-span proofs, retaining the actual coefficient-model integrals. -/

noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding UnequalRankAdjacentBlockSpanStatement UnequalRankAnalyticStatement UnequalRankBlockZeroGammaExistenceStatement UnequalRankCommonGeneratorStatement UnequalRankCompactSupportStatement UnequalRankComplementaryTransferStatement UnequalRankFiniteExpansionStatement UnequalRankFourierSmearingStatement UnequalRankFunctionalEquationStatement UnequalRankGammaPropagationStatement UnequalRankIwasawaSupportStatement diagonal_abs_bound diagonal_abs_last exists_compactOpen_rectangular_subgroup normalizedAbs_prod normalizedAbsoluteValue normalizedAbsoluteValue_apply unequalRankAdjacentBlockSpan unequalRankCompactSupport unequalRankComplementaryTransfer unequalRankFiniteExpansion unequalRankFiniteExpansion_of_cosetExpansion unequalRankFourierSmearingStatement unequalRankGammaPropagation unequalRankIwasawaSupport unequalRank_coefficient_invariant
open Langlands.AllField.RankinSelberg

open MeasureTheory
open Langlands.HarmonicAnalysis hiding PadicLatticeFourierStatement PadicLatticeGeometryStatement PadicLatticeHaarStatement PadicLatticeSchwartzExpansionStatement PadicRectangularHaarScalingStatement PadicRowFourierCutoffStatement PadicRowFourierSurjectivityStatement PadicSelfDualMeasureExistsStatement padicLatticeFourier padicLatticeGeometry padicLatticeHaar padicLatticeSchwartzExpansion padicRowFourierCutoff padicRowFourierSurjectivity padicScalarHaarScaling padicSchwartzBruhat_exists_additiveLattice_invariant padicSelfDualMeasureExists
open Langlands.AllField.HarmonicAnalysis
open Langlands.Whittaker hiding SmoothSimpleRootSupportStatement smoothSimpleRootSupport
open Langlands.AllField.Whittaker
open Langlands.GeneralLinear
open Langlands.QuotientIntegration

universe uF uV uW

section FixedData

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  [MeasurableSpace F] {n r : ℕ}
  [MeasurableSpace (LeftUnipotentQuotient n F)]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {hnr : n < r} {q : ℕ} {ψ : UnitaryAdditiveCharacter F}
  {abv : AbsoluteValue F ℝ} {μ : Measure (LeftUnipotentQuotient n F)}
  {ν : AdditiveHaarMeasure F}
  {π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V}
  {σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W}
  {ℓ : glFunctionals ψ r π} {ℓ' : glInverseFunctionals ψ n σ}

end FixedData

section PadicAssembly

variable (F : Type uF) [Field F] (T : LocalFieldData F)

/-- The literal block-zero gamma equation propagates to all complementary
blocks with the same supplied rational multiplier and the same measures. -/
theorem unequalRankGammaPropagation (n r : ℕ) :
    UnequalRankGammaPropagationStatement.{uF, uV, uW} F T n r := by
  have hTransfer := unequalRankComplementaryTransfer.{uF, uV, uW} F T n r
  have hSpan := unequalRankAdjacentBlockSpan.{uF, uV, uW} F T n r
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := IsTopologicalAddGroup.rightUniformSpace F
  let := isUniformAddGroup_of_addCommGroup (G := F)
  let := rowFourierCutoff_nonarchimedean (K := F)
  let := borel F
  let : BorelSpace F := ⟨rfl⟩
  let := borel (Langlands.GeneralLinear (n + 1) F)
  let : BorelSpace (Langlands.GeneralLinear (n + 1) F) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1) F)
  let : BorelSpace (upperUnipotent (n + 1) F) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient n F)
  let : BorelSpace (LeftUnipotentQuotient n F) := ⟨rfl⟩
  intro hnr ψ hInv μ hμ ν hν V _ _ W _ _ π σ hπ hσ ℓ ℓ' hℓ hℓ' G hZero
  exact unequalRankGammaEquation_of_pairedTransfer
    (hSpan hnr ψ μ hμ ν V W π σ hπ hσ ℓ ℓ' hℓ hℓ')
    (hTransfer hnr ψ μ hμ ν hν V W π σ hπ hσ ℓ ℓ' hℓ hℓ') hZero

end PadicAssembly

end Langlands.AllField.RankinSelberg
