import Langlands.Correspondence.AssemblyTheorems
import Langlands.Correspondence.AssemblyEpsilonReduction
import Langlands.ClassFieldTheory.Local.WeilReciprocityUniquenessStatement

/-!
# Combining reciprocity comparison with fixed-system epsilon inheritance

This conditional reduction retains the single local-constant system witnessed
by the given supercuspidal correspondence. Its two premises remain separate
proof obligations.
-/

namespace Langlands.Correspondence

universe uF uP uA

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- The conditional reduction of assembled epsilon inheritance to geometric
reciprocity uniqueness and inheritance for the witnessed fixed system. -/
def AssemblyEpsilonInheritanceReductionStatement : Prop :=
  LocalClassField.GeometricWeilReciprocityUniqueness.{uF} →
    AssemblyPairEpsilonSystemInheritance.{uF, uP, uA} F →
      AssemblyEpsilonInheritanceStatement.{uF, uP, uA} F

/-- Geometric reciprocity uniqueness and epsilon inheritance at the witnessed
system imply the unchanged assembled epsilon-inheritance statement. -/
theorem assemblyEpsilonInheritance_of_geometricUniqueness_and_systemInheritance
    : AssemblyEpsilonInheritanceReductionStatement.{uF, uP, uA} F := by
  intro hU hI c0 c e hc0 hc he
  obtain ⟨e0, he0, _, _, _, eC, ε, hε, hbase, hcompat⟩ := hc0.2.2
  have heq : e = e0 :=
    hU p F F.canonicalTopologicalData e e0 he he0
  refine ⟨eC, ε, hε, ?_, hI c0 c eC ε hε hc0 hc hcompat⟩
  simpa only [heq] using hbase

end Langlands.Correspondence
