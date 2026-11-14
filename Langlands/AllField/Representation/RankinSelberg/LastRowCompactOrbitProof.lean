import Langlands.Representation.RankinSelberg.LastRowCompactOrbitProof
import Langlands.AllField.Representation.RankinSelberg.LastRowCompactOrbitStatement
/-!
# Proof of the exact compact open orbit of the last row

The geometry is proved over any Hausdorff topological field and then applied to the
topology supplied by a p-adic field realization. See the paired Markdown for the route.
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding LastRowCompactOrbitStatement lastRowCompactOrbit
open Langlands.AllField.RankinSelberg

open _root_.Topology
open Langlands.GeneralLinear
open scoped Matrix

universe uF

section Algebra


end Algebra

section Topology




end Topology

section Indicator


end Indicator

/-- The published last-row compact open orbit statement holds for every supplied
p-adic field realization and every rank. -/
theorem lastRowCompactOrbit 
    (F : Type uF) [Field F] (T : LocalFieldData F) (n : ℕ) :
    LastRowCompactOrbitStatement.{uF} F T n := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  have : T2Space F := T.fieldT2
  exact fun J hJ => lastRowCompactOrbit_of_field n J hJ

end Langlands.AllField.RankinSelberg
