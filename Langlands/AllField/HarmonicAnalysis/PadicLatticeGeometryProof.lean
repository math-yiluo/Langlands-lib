import Langlands.HarmonicAnalysis.PadicLatticeGeometryProof
import Langlands.AllField.HarmonicAnalysis.PadicLatticeGeometryStatement
import Langlands.AllField.Representation.RankinSelberg.ZeroRowLastRowCutoffProof
/-!
# Compact-open valuation lattices for every supplied local-field topology

The lattice conclusions reuse the published supplied-topology geometry lemmas.
Total disconnectedness follows from the Hausdorff nonarchimedean additive group.
-/

namespace Langlands.AllField.HarmonicAnalysis
open Langlands.HarmonicAnalysis hiding PadicLatticeGeometryStatement PadicRectangularHaarScalingStatement padicLatticeGeometry padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis

universe u

/-- Every supplied local-field topology is totally disconnected, and every integer
valuation lattice is compact and open in that same topology. -/
theorem padicLatticeGeometry 
    (F : Type u) [Field F] (T : LocalFieldData F) :
    PadicLatticeGeometryStatement F T := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  refine ⟨?_, fun m => ⟨T.isCompact_additiveLattice m, T.isOpen_additiveLattice m⟩⟩
  let := T.fieldT2
  let : NonarchimedeanRing F := by
    convert! ValuativeRel.nonarchimedeanRing F using 1
    exact Valuation.toTopologicalSpace_eq (ValuativeRel.valuation F)
  infer_instance

end Langlands.AllField.HarmonicAnalysis
