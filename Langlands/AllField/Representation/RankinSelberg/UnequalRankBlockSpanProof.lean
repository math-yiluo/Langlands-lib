import Langlands.Representation.RankinSelberg.UnequalRankBlockSpanProof
import Langlands.AllField.HarmonicAnalysis.PadicRowFourierSurjectivityProof
import Langlands.AllField.Representation.RankinSelberg.FunctionalEquationStatement
import Langlands.AllField.Representation.RankinSelberg.UnequalRankBlockSpanStatement
import Langlands.AllField.Representation.RankinSelberg.UnequalRankCompactSupportProof
import Langlands.AllField.Representation.RankinSelberg.UnequalRankFiniteExpansionProof
import Langlands.AllField.Representation.RankinSelberg.UnequalRankFourierSmearingProof
/-! Equality of adjacent JPSS block spans using supplied-measure integration
and Fourier smearing in the original coefficient model. -/

noncomputable section

namespace Langlands.AllField.RankinSelberg.AdjacentBlockReduction
open Langlands.RankinSelberg.AdjacentBlockReduction hiding adjacentBlockSpan_of_fourier adjacentBlockSpan_of_support_fourier
open Langlands.AllField.RankinSelberg.AdjacentBlockReduction
open Langlands.RankinSelberg hiding UnequalRankAdjacentBlockSpanStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement UnequalRankCompactSupportStatement UnequalRankFiniteExpansionStatement UnequalRankFourierSmearingStatement UnequalRankFunctionalEquationStatement UnequalRankIwasawaSupportStatement diagonal_abs_bound diagonal_abs_last exists_compactOpen_rectangular_subgroup normalizedAbs_prod normalizedAbsoluteValue normalizedAbsoluteValue_apply unequalRankAdjacentBlockSpan unequalRankCompactSupport unequalRankFiniteExpansion unequalRankFiniteExpansion_of_cosetExpansion unequalRankFourierSmearingStatement unequalRankIwasawaSupport unequalRank_coefficient_invariant
open Langlands.AllField.RankinSelberg

open MeasureTheory
open Langlands.HarmonicAnalysis hiding PadicLatticeFourierStatement PadicLatticeGeometryStatement PadicLatticeHaarStatement PadicLatticeSchwartzExpansionStatement PadicRectangularHaarScalingStatement PadicRowFourierSurjectivityStatement PadicSelfDualMeasureExistsStatement padicLatticeFourier padicLatticeGeometry padicLatticeHaar padicLatticeSchwartzExpansion padicRowFourierSurjectivity padicScalarHaarScaling padicSchwartzBruhat_exists_additiveLattice_invariant padicSelfDualMeasureExists
open Langlands.AllField.HarmonicAnalysis

section LastRowCoefficient

open Langlands.Whittaker hiding SmoothSimpleRootSupportStatement smoothSimpleRootSupport
open Langlands.AllField.Whittaker

universe uF uV

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

end LastRowCoefficient

section AdjacentIntegral

open Langlands.Whittaker hiding SmoothSimpleRootSupportStatement smoothSimpleRootSupport
open Langlands.AllField.Whittaker

universe uF uV

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  [T2Space F] [MeasurableSpace F] [BorelSpace F]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

universe uW

end AdjacentIntegral

section PadicAssembly

open Langlands.Whittaker hiding SmoothSimpleRootSupportStatement smoothSimpleRootSupport
open Langlands.AllField.Whittaker
open Langlands.GeneralLinear

universe uF uV uW

/-- The exact published adjacent-span target reduces to uniform compact support
and Fourier preimages for the supplied Haar. The published smearing theorem
constructs every needed same-model cutoff. -/
theorem adjacentBlockSpan_of_support_fourier 
    (F : Type uF) [Field F] (T : LocalFieldData F) (n r : ℕ)
    (hsupport : ∀ j k, UnequalRankCompactSupportStatement.{uF,uV} F T n (j + 1) k)
    (hfourier : PadicRowFourierSurjectivityStatement F T (n + 1)) :
    UnequalRankAdjacentBlockSpanStatement.{uF,uV,uW} F T n r := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let := T.sigmaCompactSpace
  let := T.secondCountableTopology
  let : NonarchimedeanRing F := by
    convert (ValuativeRel.nonarchimedeanRing F) using 1
    exact (ValuativeRel.valuation F).toTopologicalSpace_eq
  let := borel F
  let : BorelSpace F := ⟨rfl⟩
  let := borel (Langlands.GeneralLinear (n + 1) F)
  let : BorelSpace (Langlands.GeneralLinear (n + 1) F) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1) F)
  let : BorelSpace (upperUnipotent (n + 1) F) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient n F)
  let : BorelSpace (LeftUnipotentQuotient n F) := ⟨rfl⟩
  intro _ ψ _ μ _ ν V _ _ W _ _ π σ hπ _ ℓ ℓ' hℓ _ j k hr
  have h₁ : r = n + ((j + 1) + k + 1) := by omega
  have h₂ : r = n + (j + (k + 1) + 1) := by omega
  have hs : ∀ f : (coefficientModel π ℓ).toSubmodule,
      ∃ C : Set (Matrix (Fin (j + 1)) (Fin (n + 1)) F), IsCompact C ∧
        ∀ g X, f.val.val (blockMatrixAt (j + 1) k h₁ g X) ≠ 0 → X ∈ C := by
    subst h₁
    exact hsupport j k ψ V π hπ ℓ hℓ
  have hc : ∀ (f : (coefficientModel π ℓ).toSubmodule)
        (Φ : SchwartzBruhat (Fin (n + 1) → F)),
      ∃ f₁ : (coefficientModel π ℓ).toSubmodule, ∀ g X,
        f₁.val.val (blockMatrixAt (j + 1) k h₁ g X) =
          Φ (X (Fin.last j)) * f.val.val (blockMatrixAt (j + 1) k h₁ g X) := by
    subst h₁
    intro f Φ
    obtain ⟨κ, hpair⟩ := hfourier ψ ν Φ
    obtain ⟨f₁, _, hpoint⟩ := unequalRankFourierSmearingStatement F T n j k
      ψ ν V π hπ.1.1 ℓ f κ Φ hpair
    exact ⟨f₁, hpoint⟩
  exact congrArg zetaSpan (adjacent_values_eq_of_support_cutoff
    ν n r j k h₁ h₂ T.residueCardinality ψ (normalizedAbsoluteValue T) μ
    π hπ.1.1 ℓ σ ℓ' hs hc)

/-- The published compact-support theorem discharges the support premise.
Only Fourier preimages for every supplied Haar remain as a hypothesis. -/
theorem adjacentBlockSpan_of_fourier 
    (F : Type uF) [Field F] (T : LocalFieldData F) (n r : ℕ)
    (hfourier : PadicRowFourierSurjectivityStatement F T (n + 1)) :
    UnequalRankAdjacentBlockSpanStatement.{uF,uV,uW} F T n r :=
  adjacentBlockSpan_of_support_fourier F T n r
    (fun j k => unequalRankCompactSupport.{uF,uV} F T n (j + 1) k) hfourier

end PadicAssembly

end Langlands.AllField.RankinSelberg.AdjacentBlockReduction

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding UnequalRankAdjacentBlockSpanStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement UnequalRankCompactSupportStatement UnequalRankFiniteExpansionStatement UnequalRankFourierSmearingStatement UnequalRankFunctionalEquationStatement UnequalRankIwasawaSupportStatement diagonal_abs_bound diagonal_abs_last exists_compactOpen_rectangular_subgroup normalizedAbs_prod normalizedAbsoluteValue normalizedAbsoluteValue_apply unequalRankAdjacentBlockSpan unequalRankCompactSupport unequalRankFiniteExpansion unequalRankFiniteExpansion_of_cosetExpansion unequalRankFourierSmearingStatement unequalRankIwasawaSupport unequalRank_coefficient_invariant
open Langlands.AllField.RankinSelberg

universe uF uV uW

/-- Adjacent unequal-rank JPSS blocks have equal Laurent spans for every
supplied topology and additive Haar measure. -/
theorem unequalRankAdjacentBlockSpan 
    (F : Type uF) [Field F] (T : LocalFieldData F) (n r : ℕ) :
    UnequalRankAdjacentBlockSpanStatement.{uF,uV,uW} F T n r :=
  Langlands.AllField.RankinSelberg.AdjacentBlockReduction.adjacentBlockSpan_of_fourier F T n r
    (Langlands.AllField.HarmonicAnalysis.padicRowFourierSurjectivity F T (n + 1))

end Langlands.AllField.RankinSelberg
