import Langlands.HarmonicAnalysis.Conductor

/-!
# Compact-open valuation lattices for a supplied p-adic topology

A derived proposition target: for every supplied topology on a finite extension
of `ℚ_p`, the space is totally disconnected and every actual valuation lattice
`T.additiveLattice m = π^(-m) O` is compact and open. No proof is supplied here.
-/

namespace Langlands.HarmonicAnalysis

universe u

/-- The supplied p-adic topology is totally disconnected, and for every integer
`m` the existing valuation lattice `T.additiveLattice m` is both compact and open
in that topology. All three facts are conclusions; none is a hypothesis. -/
def PadicLatticeGeometryStatement {p : ℕ} [Fact p.Prime]
    (F : PadicField.{u} p) (T : F.TopologicalData) : Prop :=
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  TotallyDisconnectedSpace F.Carrier ∧
    ∀ m : ℤ, IsCompact (T.additiveLattice m : Set F.Carrier) ∧
      IsOpen (T.additiveLattice m : Set F.Carrier)

end Langlands.HarmonicAnalysis
