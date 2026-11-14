import Langlands.Representation.RankinSelberg.AdjacentRankInvariantApproximation
import Langlands.AllField.Representation.RankinSelberg.AdjacentRankNormalizedSection
/-! One compact open level for all full-rank approximating normalized sections. -/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AllField.RankinSelberg.Padic
open Langlands.RankinSelberg.Padic hiding AdjacentRankInvariantApproximationData adjacentRankInvariantApproximation adjacentRankLowerCompactRepresentation adjacentRankLowerInducingCoordinates adjacentRankLowerTensorCoordinates_action adjacentRankLowerTensorRepresentation adjacentRankNormalizedSection adjacentRankNormalizedSectionTensor adjacentRankNormalizedSectionTensor_tmul adjacentRankNormalizedSection_eval adjacentRankNormalizedSection_right adjacentSectionFieldTopology adjacentSectionGLBorel adjacentSectionGLMeasurable adjacentSectionLocalField adjacentSectionT2 adjacentSectionValuativeRel exists_adjacentRankTestWeightLevel invariantApproximationGLLocallyCompact invariantApproximationGLNonarch invariantApproximationLocalField invariantApproximationNonarchRing invariantApproximationSecondCountable invariantApproximationT2 invariantApproximationTopology invariantApproximationValuativeRel nonempty_adjacentRankInvariantApproximation
open Langlands.AllField.RankinSelberg.Padic
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement LastRowCompactOrbitStatement QuotientHaarExistenceStatement RankOneWhittakerTypeStatement TwoBlockWhittakerDeformationStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement adjacentRankDeterminantWeight adjacentRankDeterminantWeight_apply adjacentRankDeterminantWeight_locallyConstant adjacentRankLowerScalarProjection adjacentRankLower_determinantComplexPower adjacentRankLower_halfModulus adjacentRankLower_weightRatio isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt lastRowCompactOrbit normalizedAbsoluteValue normalizedAbsoluteValue_apply rankOneCharacter_isOfWhittakerType rankOneExtensionCharacter rankOneExtensionCharacter_isOfWhittakerType rankOneExtensionCharacter_isSmooth rankOneWhittakerType twoBlockDeformedBlocks twoBlockDeformedBlocks_zero twoBlockDeformedInduced
open Langlands.AllField.RankinSelberg

open Set Filter _root_.Topology Matrix
open Langlands.HarmonicAnalysis hiding padicRectangularHaarScaling padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis

universe uF uV

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance invariantApproximationT2 : T2Space F :=
  (⟨⟩ : LocalFieldData F).fieldT2
local instance invariantApproximationSecondCountable : SecondCountableTopology F :=
  (⟨⟩ : LocalFieldData F).secondCountableTopology
local instance invariantApproximationNonarchRing : NonarchimedeanRing F := by
  convert! ValuativeRel.nonarchimedeanRing F
  exact Valuation.toTopologicalSpace_eq _
local instance invariantApproximationGLNonarch (n : ℕ) :
    NonarchimedeanGroup (GeneralLinear n F) :=
  (⟨⟩ : LocalFieldData F).generalLinearNonarchimedean n
local instance invariantApproximationGLLocallyCompact (n : ℕ) :
    LocallyCompactSpace (GeneralLinear n F) :=
  (⟨⟩ : LocalFieldData F).generalLinearLocallyCompactSpace n

variable {r : ℕ}

/-- A compact open subgroup fixing a Schwartz test and killing a smooth scalar weight. -/
theorem exists_adjacentRankTestWeightLevel
    (Φ : SchwartzBruhat (Matrix (Fin (r + 1)) (Fin (r + 2)) F))
    (θ : Induction.SmoothCharacter ℂ (GeneralLinear (r + 2) F)) :
    ∃ J : OpenSubgroup (GeneralLinear (r + 2) F),
      IsCompact (J : Set (GeneralLinear (r + 2) F)) ∧
      (∀ M (k : J.toSubgroup), Φ (M * k.val.val) = Φ M) ∧
      ∀ k : J.toSubgroup, θ.toMonoidHom k.val = 1 := by
  obtain ⟨U, hU⟩ := rectangularTestSmooth Φ
  let K : OpenSubgroup (GeneralLinear (r + 2) F) :=
    ⟨θ.toMonoidHom.ker, θ.isOpen_ker⟩
  obtain ⟨J, hJc, hJ⟩ := compactOpenSubgroupBasis
    (GeneralLinear (r + 2) F) (↑(U ⊓ K))
    ((U ⊓ K).isOpen.mem_nhds (U ⊓ K).one_mem)
  exact ⟨J, hJc, fun M k => hU k.val (hJ k.property).1 M,
    fun k => (hJ k.property).2⟩

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (σ : Representation ℂ (GeneralLinear (r + 1) F) V)
  (χ : Quasicharacter F)

/-- Full-rank tests approximating one Schwartz test, all of whose actual normalized
sections lie at one compact open level, uniformly in the original vector. -/
structure AdjacentRankInvariantApproximationData (hσ : IsSmooth σ)
    (Φ : SchwartzBruhat (Matrix (Fin (r + 1)) (Fin (r + 2)) F)) where
  level : OpenSubgroup (GeneralLinear (r + 2) F)
  isCompact_level : IsCompact (level : Set (GeneralLinear (r + 2) F))
  tests : ℕ → adjacentRankCompactTests (r + 1) F
  invariant : ∀ n M (k : level.toSubgroup),
    (tests n).val (M * k.val.val) = (tests n).val M
  norm_le : ∀ n M, ‖(tests n).val M‖ ≤ ‖Φ M‖
  eventually_eq : ∀ M, AdjacentRankFullRank M →
    ∀ᶠ n in atTop, (tests n).val M = Φ M
  fixed : ∀ n v, adjacentRankNormalizedSection F σ χ hσ (tests n) v ∈
    fixedVectors
      ((⟨⟩ : LocalFieldData F).normalizedOppositeParabolicInduced (adjacentRankLowerShape r)
        ((adjacentRankLowerShape r).blockTensor
          (Shahidi.pairFamily σ (rankOneExtensionCharacter.{uF, uV} F χ))))
      level.toSubgroup

/-- Invariant cutoff tests exist at one compact open level of the exact host induction. -/
theorem nonempty_adjacentRankInvariantApproximation (hσ : IsSmooth σ)
    (Φ : SchwartzBruhat (Matrix (Fin (r + 1)) (Fin (r + 2)) F)) :
    Nonempty (AdjacentRankInvariantApproximationData F σ χ hσ Φ) := by
  let θ := adjacentRankDeterminantWeight (⟨⟩ : LocalFieldData F) χ
    (r + 2) ((r + 1 : ℕ) / 2)
  obtain ⟨J, hJc, hΦ, hθ⟩ := exists_adjacentRankTestWeightLevel F Φ θ
  obtain ⟨Ψ, hΨ, hnorm, heq⟩ :=
    exists_adjacentRankFullRankTestApproximation J.toSubgroup hJc Φ hΦ
  refine ⟨⟨J, hJc, Ψ, hΨ, hnorm, heq, ?_⟩⟩
  intro n v
  change ∀ k : J.toSubgroup,
    (⟨⟩ : LocalFieldData F).normalizedOppositeParabolicInduced (adjacentRankLowerShape r)
      ((adjacentRankLowerShape r).blockTensor
        (Shahidi.pairFamily σ (rankOneExtensionCharacter.{uF, uV} F χ))) k.val
      (adjacentRankNormalizedSection F σ χ hσ (Ψ n) v) =
      adjacentRankNormalizedSection F σ χ hσ (Ψ n) v
  intro k
  have ht : adjacentRankCompactTestTranslate k.val (Ψ n) = Ψ n := by
    apply Subtype.ext
    ext M
    exact hΨ n M k
  rw [adjacentRankNormalizedSection_right, ht]
  change (θ.toMonoidHom k.val : ℂ) • _ = _
  rw [hθ k, Units.val_one]
  exact one_smul ℂ _

/-- Choose one invariant approximation, retaining the exact normalized sections on V. -/
def adjacentRankInvariantApproximation (hσ : IsSmooth σ)
    (Φ : SchwartzBruhat (Matrix (Fin (r + 1)) (Fin (r + 2)) F)) :
    AdjacentRankInvariantApproximationData F σ χ hσ Φ :=
  Classical.choice (nonempty_adjacentRankInvariantApproximation F σ χ hσ Φ)

end Langlands.AllField.RankinSelberg.Padic
