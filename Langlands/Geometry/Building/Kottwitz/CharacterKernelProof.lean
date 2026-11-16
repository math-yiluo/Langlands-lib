import Langlands.Geometry.Building.Kottwitz.CharacterKernelReduction
import Langlands.Geometry.Building.Kottwitz.TorusCharacterKernelProof
import Langlands.Geometry.Building.Kottwitz.CocenterTargetTorsionProof
import Langlands.Geometry.Building.Kottwitz.ReductiveFunctorialityProof
import Langlands.Geometry.Building.Kottwitz.ZExtensionKernelProof

/-! # KP Lemma 11.5.2: proof of the character-valuation kernel identity -/

universe u

namespace Langlands.Geometry.Building.Kottwitz

/-- KP Lemma 11.5.2: the rational-character valuation kernel is the inverse image
of invariant inertia torsion under the rational Kottwitz homomorphism. -/
theorem characterKernel : CharacterKernelStatement.{u} :=
  CharacterKernelInputs.characterKernel
    ⟨torusCharacterKernel, cocenterTargetTorsion_proof,
      reductiveKottwitzFunctoriality, reductiveKottwitzDescent_assembled⟩

end Langlands.Geometry.Building.Kottwitz
