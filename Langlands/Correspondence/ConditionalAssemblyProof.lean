import Langlands.Correspondence.AssemblyConstruction
import Langlands.Correspondence.AssemblyWellDefinedProof
import Langlands.Correspondence.AssemblyBijectiveProof
import Langlands.Correspondence.AssemblyOperationProof
import Langlands.Correspondence.AssemblyLInheritanceProof
import Langlands.Correspondence.AssemblyEpsilonInheritanceProof

/-!
# The conditional assembly theorem

Henniart 2002, Theorem 1.5 and §2.9: every supercuspidal correspondence has an
assembly, and every assembly is a full correspondence. The proof applies the
published reduction `conditionalAssembly_of_fivePrerequisites` to the published
proofs of its five prerequisite propositions.
-/

namespace Langlands.Correspondence

universe uF uP uA

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- **Conditional assembly** (Henniart 2002, Theorem 1.5 and §2.9). -/
theorem conditionalAssembly : ConditionalAssemblyStatement.{uF, uP, uA} F :=
  conditionalAssembly_of_fivePrerequisites F
    (assemblyWellDefined.{uF, uP, uA} F)
    (assemblyBijective.{uF, uP, uA} F)
    (assemblyOperation.{uF, uP, uA} F)
    (assemblyLInheritance.{uF, uP, uA} F)
    (assemblyEpsilonInheritance.{uF, uP, uA} F)

end Langlands.Correspondence
