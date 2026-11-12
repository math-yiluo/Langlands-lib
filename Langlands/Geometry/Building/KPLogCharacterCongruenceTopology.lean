import Langlands.Geometry.Building.KPCharacterCongruence
import Langlands.LocalField.LogCongruenceTopology
import Mathlib.Topology.Algebra.OpenSubgroup

/-! # Open logarithmic character congruence subgroups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme Langlands.LocalField
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj NNReal

namespace Langlands.Geometry.Building

variable {k : Type u} [NormedField k] [IsUltrametricDist k]
  (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffine G.X.left]
  [Module.Finite ℤ (rationalCharacters G)]

local instance : TopologicalSpace (rationalPoints G) := rationalPointTopology k G.X

/-- Logarithmic actual-character congruence subgroups are open in the canonical
rational-point topology. -/
theorem isOpen_characterCongruence_log (c : ℝ) (hc : 0 < c) (r : ℝ≥0) :
    IsOpen (characterCongruence
      (logAdditiveValuation (NormedField.valuation (K := k)) c hc) G r :
        Set (rationalPoints G)) :=
  isOpen_characterCongruence _ r (isOpen_addValuationUnitFiltration_log c hc r)

/-- The logarithmic character congruence subgroup, bundled with its openness. -/
def logCharacterCongruenceOpenSubgroup (c : ℝ) (hc : 0 < c) (r : ℝ≥0) :
    OpenSubgroup (rationalPoints G) where
  toSubgroup := characterCongruence
    (logAdditiveValuation (NormedField.valuation (K := k)) c hc) G r
  isOpen' := isOpen_characterCongruence_log G c hc r

@[simp] theorem logCharacterCongruenceOpenSubgroup_toSubgroup
    (c : ℝ) (hc : 0 < c) (r : ℝ≥0) :
    (logCharacterCongruenceOpenSubgroup G c hc r).toSubgroup =
      characterCongruence
        (logAdditiveValuation (NormedField.valuation (K := k)) c hc) G r := rfl

end Langlands.Geometry.Building
