import Langlands.Correspondence.AssemblyLCharacterizationReduction
import Langlands.Correspondence.AssemblySquareIntegrablePreimageReduction
import Langlands.Correspondence.AssemblyWellDefinedProof
import Langlands.Correspondence.AssemblyBijectiveProof
import Langlands.Correspondence.AssemblyLInheritanceProof
import Langlands.Representation.RankinSelberg.SquareIntegrablePoleOrderCharacterizationProof
import Langlands.Representation.Classification.MultisegmentHeadClassificationProof

/-!
# Characterization of the assembly by lower-rank L-factors

Henniart 2002, Theorem 1.8. The published reduction
`assemblyLCharacterization_of_ingredients` derives the target from five
ingredients. Each is now a published Library theorem: well-definedness,
bijectivity and L-inheritance of the assembly, Henniart's Theorem 1.7(b), and
(through `assemblySquareIntegrablePreimage_of_headClassification`) the
multisegment head classification.
-/

noncomputable section

namespace Langlands.Correspondence

universe uF uP uA

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- The five ingredients of the reduction, all proved. -/
theorem assemblyLCharacterizationIngredients :
    AssemblyLCharacterizationIngredients.{uF, uP, uA} F :=
  ⟨assemblyWellDefined F, assemblyBijective F, assemblyLInheritance F,
    RankinSelberg.squareIntegrablePoleOrderCharacterization.{uF, uA, uA},
    assemblySquareIntegrablePreimage_of_headClassification F
      (Classification.multisegmentHeadClassification.{uF, uA} F F.canonicalTopologicalData)⟩

/-- **Henniart 2002, Theorem 1.8.** Let `c0` be a supercuspidal correspondence and
`ψ` a nontrivial additive character. If a full map `τ` extends `c0` and has the
right pair L-factors at `ψ` for every non-irreducible-Weil class against every
indecomposable class of smaller rank, then `τ` is the assembly of `c0`, and every
assembly of `c0` equals `τ`. -/
theorem assemblyLCharacterization : AssemblyLCharacterizationStatement.{uF, uP, uA} F :=
  assemblyLCharacterization_of_ingredients (assemblyLCharacterizationIngredients F)

end Langlands.Correspondence
