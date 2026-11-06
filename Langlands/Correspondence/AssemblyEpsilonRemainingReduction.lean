import Langlands.Correspondence.AssemblyEpsilonCombination
import Langlands.Correspondence.ArithmeticEpsilonDirectSum
import Langlands.ClassFieldTheory.Local.WeilReciprocityUniquenessProof

/-!
# Remaining premises for assembled epsilon inheritance

The published geometric reciprocity uniqueness and arithmetic direct-sum
theorems discharge those two premises of the earlier reductions. Multisegment
datum matching and segment-pair inheritance remain explicit assumptions.
-/

namespace Langlands.Correspondence

universe uF uP uA

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- The system witnessed by a supercuspidal correspondence can be based at
any supplied geometric reciprocity candidate. -/
theorem IsSupercuspidalCorrespondence.factorCompatibility_of_geometricReciprocity
    {c0 : SupercuspidalMap.{uF, uP, uA} F} {e : ReciprocityCandidate F}
    (hc0 : IsSupercuspidalCorrespondence F c0)
    (he : IsGeometricReciprocity F e) :
    SupercuspidalFactorCompatibility F e c0 := by
  obtain ⟨e0, he0, _, _, _, eC, ε, hε, hbase, hcompat⟩ := hc0.2.2
  have heq : e = e0 :=
    LocalClassField.geometricWeilReciprocityUniqueness
      p F F.canonicalTopologicalData e e0 he he0
  refine ⟨eC, ε, hε, ?_, hcompat⟩
  simpa only [heq] using hbase

/-- Fixed-system epsilon inheritance implies the original assembly target,
using the proved geometric reciprocity uniqueness theorem. -/
theorem assemblyEpsilonInheritance_of_systemInheritance
    (hI : AssemblyPairEpsilonSystemInheritance.{uF, uP, uA} F) :
    AssemblyEpsilonInheritanceStatement.{uF, uP, uA} F :=
  assemblyEpsilonInheritance_of_geometricUniqueness_and_systemInheritance F
    LocalClassField.geometricWeilReciprocityUniqueness hI

/-- The two remaining representation-theoretic premises imply assembled
epsilon inheritance, with no separate uniqueness or multiplicativity premise. -/
def AssemblyEpsilonRemainingReductionStatement : Prop :=
  MultisegmentHeadDatumMatching.{uF, uA} F →
    SupercuspidalSegmentPairInheritance.{uF, uP, uA} F →
      AssemblyEpsilonInheritanceStatement.{uF, uP, uA} F

/-- Combine the published arithmetic and reciprocity proofs with datum matching
and segment-pair inheritance. The latter two premises remain explicit. -/
theorem assemblyEpsilonInheritance_of_datumMatching_and_segmentPairs :
    AssemblyEpsilonRemainingReductionStatement.{uF, uP, uA} F := by
  intro hP hS
  apply assemblyEpsilonInheritance_of_systemInheritance F
  apply assemblyPairEpsilonSystemInheritance_of_segmentPairs F hP ?_ hS
  intro eC ε hε
  exact isArithmeticPairEpsilonFactor_directSum F eC ε hε

end Langlands.Correspondence
