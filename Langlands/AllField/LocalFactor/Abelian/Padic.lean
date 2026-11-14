import Langlands.LocalFactor.Abelian.Padic
import Langlands.AllField.LocalFactor.Abelian.Definitions
/-!
# Callable rank-one local-factor expressions

Concrete expressions for the abelian theorem family, using the actual
conductors constructed by `Langlands.HarmonicAnalysis.Conductor`.
No functional equation or nonabelian constant system is assumed or chosen.

Worker 33 authored the callable expressions and conductor bridges. Worker 20
connects them to the convergent abelian construction and supplies rational
L-factors with restricted evaluation.
-/

noncomputable section

open MeasureTheory Filter
open scoped Topology WithZero

namespace Langlands.AllField.LocalFactor.PadicAbelian
open Langlands.LocalFactor.PadicAbelian hiding SelfDualHaar uniformizerUnit uniformizerUnit_coe uniformizerUnit_ord uniformizerUnit_zpow_abs uniformizerUnit_zpow_value
open Langlands.LocalFactor.LocalAbelian (uniformizerUnit uniformizerUnit_coe uniformizerUnit_ord uniformizerUnit_zpow_abs uniformizerUnit_zpow_value)
open Langlands.AllField.LocalFactor.PadicAbelian
open Langlands.LocalFactor
open Langlands.AllField.LocalFactor

universe u

variable {F : Type u} [Field F] (T : LocalFieldData F)

local notation "MultiplicativeCharacter" =>
  @HarmonicAnalysis.Quasicharacter F _ T.topology
local notation "AdditiveCharacter" =>
  @HarmonicAnalysis.UnitaryAdditiveCharacter F _ T.topology

section Rational

open _root_.Polynomial

end Rational

section ConstructionBridges

local notation "LocalHaar" =>
  @HarmonicAnalysis.AdditiveHaarMeasure F _ T.topology
    (@borel F T.topology)

/-- Actual Haar measures satisfying the intrinsic Fourier self-duality predicate.
This subtype does not assert that such a measure exists. -/
def SelfDualHaar (ψ : AdditiveCharacter) :=
  {μ : LocalHaar //
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := IsTopologicalAddGroup.rightUniformSpace F
    letI := isUniformAddGroup_of_addCommGroup (G := F)
    letI : NonarchimedeanRing F := by
      convert! ValuativeRel.nonarchimedeanRing F
      exact Valuation.toTopologicalSpace_eq _
    letI : MeasurableSpace F := borel F
    letI : BorelSpace F := ⟨rfl⟩
    HarmonicAnalysis.IsSelfDual ψ μ}

end ConstructionBridges

end Langlands.AllField.LocalFactor.PadicAbelian
