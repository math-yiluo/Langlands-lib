import Langlands.HarmonicAnalysis.PadicLatticeGeometryStatement
import Langlands.AllField.HarmonicAnalysis.Conductor
/-!
# Compact-open valuation lattices for a supplied local-field topology

A derived proposition target: for every supplied topology on a nonarchimedean local field, the space is totally disconnected and every actual valuation lattice
`T.additiveLattice m = π^(-m) O` is compact and open. No proof is supplied here.
-/

namespace Langlands.AllField.HarmonicAnalysis
open Langlands.HarmonicAnalysis hiding PadicLatticeGeometryStatement
open Langlands.AllField.HarmonicAnalysis

universe u

/-- The supplied local-field topology is totally disconnected, and for every integer
`m` the existing valuation lattice `T.additiveLattice m` is both compact and open
in that topology. All three facts are conclusions; none is a hypothesis. -/
def PadicLatticeGeometryStatement 
    (F : Type u) [Field F] (T : LocalFieldData F) : Prop :=
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  TotallyDisconnectedSpace F ∧
    ∀ m : ℤ, IsCompact (T.additiveLattice m : Set F) ∧
      IsOpen (T.additiveLattice m : Set F)

end Langlands.AllField.HarmonicAnalysis
