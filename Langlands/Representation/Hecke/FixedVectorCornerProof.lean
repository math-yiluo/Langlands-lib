import Langlands.Representation.Hecke.FixedProjectionKernelProof
import Langlands.Representation.Hecke.FixedVectorsExactProof
import Langlands.Representation.Hecke.FixedIrreducibilityProof
import Langlands.Representation.Hecke.FixedIrreducibleEquivalenceProof
import Langlands.Representation.Hecke.SimpleCornerRealizationProof

/-! # Fixed vectors and the Hecke corner: Renard III.1.5 -/

namespace Langlands.Hecke

universe u v

/-- The Proposition and Theorem of Renard III.1.5, with the published objects
and independent group and representation universes. -/
theorem fixedVectorCorner : FixedVectorCornerStatements.{u, v} :=
  ⟨fixedProjectionKernel, fixedVectorsExact, irreducibleIffFixedSimple,
    irreducibleEquivIffFixedEquiv, simpleCornerModuleRealization⟩

end Langlands.Hecke
