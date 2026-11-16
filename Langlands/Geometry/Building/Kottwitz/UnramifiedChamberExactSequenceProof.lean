import Langlands.Geometry.Building.Kottwitz.UnramifiedChamberExactSequenceReduction
import Langlands.Geometry.Building.Kottwitz.ZeroKernelAssembly
import Langlands.Geometry.Building.Kottwitz.ZExtensionKernelProof
import Langlands.Geometry.Building.Kottwitz.TorusKernelProof
import Langlands.Geometry.Building.Kottwitz.SimplyConnectedDerivedKottwitzProof
import Langlands.Geometry.Building.UnramifiedSimplyConnectedNormalizerAffineWeylProof

/-! # KP Proposition 11.6.1: proof -/

universe u

namespace Langlands.Geometry.Building.Kottwitz

/-- **KP Proposition 11.6.1.** For every supplied chamber `Cch` of the canonical building
over the maximal unramified extension, the Kottwitz map restricted to the stabilizer `P`
of `Cch` is surjective, and for every unramified zero datum `E` the intersection of its
zero subgroup with the pointwise fixer of `Cch` equals `ker κ ⊓ P`.

The proof applies the published reduction
`unramifiedChamberExactSequence_of_statements` to three proved inputs: Kottwitz existence
`reductiveKottwitzExistence_assembled`, the unramified zero-kernel identification obtained
from `unramifiedZeroKernel_of_torus_zExtension` and its four proved inputs, and the simply
connected normalizer theorem `MaximalUnramified.simplyConnectedNormalizerAffineWeyl`. -/
theorem unramifiedChamberExactSequence : UnramifiedChamberExactSequenceStatement.{u} :=
  unramifiedChamberExactSequence_of_statements reductiveKottwitzExistence_assembled
    (unramifiedZeroKernel_of_torus_zExtension torusKottwitzKernel
      simplyConnectedDerivedKottwitz_proof reductiveKottwitzExistence_assembled
      zExtensionKottwitzKernelSurjectivity)
    MaximalUnramified.simplyConnectedNormalizerAffineWeyl

end Langlands.Geometry.Building.Kottwitz
