import Langlands.HarmonicAnalysis.CharacterSeparation
import Langlands.AllField.HarmonicAnalysis.UnboundedConductorStatement
/-! # Discrete character separation and openness of principal units

Shared helpers extracted unchanged from `UnboundedConductorProof`.
-/

noncomputable section

open scoped WithZero
open Topology

namespace Langlands.AllField.HarmonicAnalysis.CharacterSeparation
open Langlands.HarmonicAnalysis.CharacterSeparation hiding principalUnits_isOpen
open Langlands.AllField.HarmonicAnalysis.CharacterSeparation
open Langlands.HarmonicAnalysis hiding PadicQuasicharacterUnboundedConductorStatement
open Langlands.AllField.HarmonicAnalysis

theorem principalUnits_isOpen 
    {F : Type*} [Field F] (T : LocalFieldData F) (n : ℕ) :
    letI := T.topology
    IsOpen (T.principalUnits n : Set Fˣ) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let e := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F
  have hval : IsOpen {x : F | T.discreteValuation x = 1} := by
    convert (Valuation.isOpen_sphere (v := ValuativeRel.valuation F)
      one_ne_zero) using 1
    ext x
    simp only [Set.mem_ofPred_eq, Valuation.restrict_eq_one_iff]
    change e (ValuativeRel.valuation F x) = 1 ↔
      ValuativeRel.valuation F x = 1
    constructor
    · intro h
      exact e.strictMono.injective (h.trans (map_one e).symm)
    · intro h
      rw [h, map_one]
  have hint : IsOpen (T.Integers : Set F) := Valuation.isOpen_integer
  convert (hval.preimage Units.continuous_val).inter
    (hint.preimage ((Units.continuous_val.sub continuous_const).div_const
      (T.uniformizer ^ (n : ℤ)))) using 1
  ext u
  exact T.mem_principalUnits_iff_div_mem_integers n u

end Langlands.AllField.HarmonicAnalysis.CharacterSeparation
