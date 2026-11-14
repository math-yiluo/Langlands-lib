import Langlands.LocalFactor.Abelian.Definitions
import Langlands.AllField.HarmonicAnalysis.ConductorSupplement
/-! The actual abelian Gauss integral on a finite p-adic field. -/

noncomputable section

open MeasureTheory Topology
open scoped WithZero WithZeroTopology

namespace Langlands.AllField.HarmonicAnalysis.Quasicharacter
open Langlands.HarmonicAnalysis.Quasicharacter
open Langlands.AllField.HarmonicAnalysis.Quasicharacter
open Langlands.HarmonicAnalysis
open Langlands.AllField.HarmonicAnalysis

universe u

end Langlands.AllField.HarmonicAnalysis.Quasicharacter

namespace Langlands.LocalFieldData
open Langlands.LocalFieldData

universe u
variable {F : Type u} [Field F] (T : LocalFieldData F)

local notation "AdditiveCharacter" =>
  @HarmonicAnalysis.UnitaryAdditiveCharacter F _ T.topology
local notation "MultiplicativeCharacter" =>
  @HarmonicAnalysis.Quasicharacter F _ T.topology
local notation "LocalHaar" =>
  @HarmonicAnalysis.AdditiveHaarMeasure F _ T.topology
    (@borel F T.topology)

/-- The actual valuation shell of elements of order `-k`. -/
def valuationShell (k : ℤ) : Set F :=
  {x | T.discreteValuation x = WithZero.exp k}

/-- A nonzero valuation shell is compact in the supplied local-field topology. -/
theorem valuationShell_compact_closed (k : ℤ) :
    letI := T.topology
    IsCompact (T.valuationShell k) ∧ IsClosed (T.valuationShell k) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let e := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F
  let γ := e.symm (WithZero.exp k)
  have hs : T.valuationShell k = {x | ValuativeRel.valuation F x = γ} := by
    ext x
    change e (ValuativeRel.valuation F x) = WithZero.exp k ↔
      ValuativeRel.valuation F x = γ
    constructor
    · intro h
      apply e.injective
      simpa [γ] using h
    · intro h
      rw [h]
      exact e.apply_symm_apply _
  rw [hs]
  have hc : IsClosed {x | ValuativeRel.valuation F x = γ} :=
    isClosed_eq IsValuativeTopology.continuous_valuation continuous_const
  exact ⟨(IsNonarchimedeanLocalField.isCompact_closedBall F γ).of_isClosed_subset
    hc (fun _x hx => hx.le), hc⟩

open Langlands.HarmonicAnalysis
open Langlands.AllField.HarmonicAnalysis

end Langlands.LocalFieldData
