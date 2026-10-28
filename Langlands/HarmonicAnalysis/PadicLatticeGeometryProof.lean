import Langlands.HarmonicAnalysis.PadicLatticeGeometryStatement
import Langlands.Representation.RankinSelberg.ZeroRowLastRowCutoffProof
import Mathlib.Topology.Algebra.Nonarchimedean.TotallyDisconnected

/-!
# Compact-open valuation lattices for every supplied p-adic topology

The lattice conclusions reuse the published supplied-topology geometry lemmas.
Total disconnectedness follows from the Hausdorff nonarchimedean additive group.
-/

namespace Langlands.HarmonicAnalysis

universe u

/-- Every supplied p-adic topology is totally disconnected, and every integer
valuation lattice is compact and open in that same topology. -/
theorem padicLatticeGeometry {p : ℕ} [Fact p.Prime]
    (F : PadicField.{u} p) (T : F.TopologicalData) :
    PadicLatticeGeometryStatement F T := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  refine ⟨?_, fun m => ⟨T.isCompact_additiveLattice m, T.isOpen_additiveLattice m⟩⟩
  let := T.fieldT2
  let : NonarchimedeanRing F.Carrier := by
    convert! ValuativeRel.nonarchimedeanRing F.Carrier using 1
    exact Valuation.toTopologicalSpace_eq (ValuativeRel.valuation F.Carrier)
  infer_instance

end Langlands.HarmonicAnalysis
