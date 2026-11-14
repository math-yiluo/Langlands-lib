import Langlands.Geometry.Building.Kottwitz.TorusCharacterKernelReduction
import Langlands.Geometry.Building.Kottwitz.TorusMapProof
import Langlands.Geometry.Building.Kottwitz.TorusNormValuation

/-! # Proof of the torus character-valuation kernel identity -/

universe u

namespace Langlands.Geometry.Building.Kottwitz

/-- Kaletha–Prasad Lemma 11.1.3 and its rational restriction, from the published
proofs of the torus Kottwitz existence statement and of the integer normalization. -/
theorem torusCharacterKernel : TorusCharacterKernelStatement.{u} :=
  TorusCharacterKernelInputs.torusCharacterKernel
    ⟨torusKottwitzExistence, normalizedIntermediateValuationStatement⟩

end Langlands.Geometry.Building.Kottwitz
