import Langlands.Representation.CuspidalSupport.RationalNormKernelSupportGeometry
import Langlands.BruhatTits.SpecialCompact.JointBasisProof

/-! # Common fixed-level coefficient support on the rational norm kernel -/

universe uF uV

namespace Langlands.CuspidalSupport

/-- The class-uniform coefficient-support step of Renard VI.3.4. For every
connected reductive group over a nonarchimedean local field, with the structural
premises of `RationalNormKernelUniformSupportStatement`, each compact open
subgroup `K` of the actual common rational-character norm kernel admits one
compact subset of the kernel containing the support of every inverse coefficient
`g ↦ ℓ (π(g⁻¹) v)`, for all actual compact irreducible smooth complex
representations `π`, all `K`-fixed vectors `v` and all `K`-invariant
algebraic-dual functionals `ℓ`. The field universe `uF` and the
representation-carrier universe `uV` are independent. -/
theorem rationalNormKernelUniformSupport :
    RationalNormKernelUniformSupportStatement.{uF, uV} :=
  rationalNormKernelUniformSupport_of_joint.{uF, uV}
    BruhatTits.SpecialCompact.jointSpecialCompactBasisExistence.{uF}

end Langlands.CuspidalSupport
