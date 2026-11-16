import Langlands.Geometry.Building.Kottwitz.ZeroKernelAssembly
import Langlands.Geometry.Building.Kottwitz.TorusKernelProof
import Langlands.Geometry.Building.Kottwitz.SimplyConnectedDerivedKottwitzProof
import Langlands.Geometry.Building.Kottwitz.ZExtensionKernelProof

/-! # The unramified Kottwitz zero-kernel equality -/

universe u

namespace Langlands.Geometry.Building.Kottwitz

/-- The zero subgroup over the maximal unramified extension is the kernel of
the constructed Kottwitz homomorphism, for every existing defining datum. -/
theorem unramifiedZeroKernel : UnramifiedZeroKernelStatement.{u} :=
  unramifiedZeroKernel_of_torus_zExtension torusKottwitzKernel
    simplyConnectedDerivedKottwitz_proof reductiveKottwitzExistence_assembled
    zExtensionKottwitzKernelSurjectivity

/-- KP Proposition 11.5.4 follows from descent of the actual zero subgroups;
the Kottwitz-map descent and unramified kernel equality are proved inputs. -/
theorem zeroKernel_of_unramifiedZeroDescent
    (hzero : UnramifiedZeroDescentStatement.{u}) :
    ZeroKernelStatement.{u} :=
  zeroKernel_of_unramified reductiveKottwitzDescent_assembled hzero unramifiedZeroKernel

end Langlands.Geometry.Building.Kottwitz
