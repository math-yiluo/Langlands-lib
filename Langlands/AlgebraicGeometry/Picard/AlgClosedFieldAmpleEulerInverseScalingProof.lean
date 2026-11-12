import Langlands.AlgebraicGeometry.Picard.AlgClosedFieldAmpleEulerInverseScalingStatement
import Langlands.AlgebraicGeometry.Picard.AlgClosedFieldAmpleEulerInverseScalingAssembly
import Langlands.AbelianScheme.FieldCubePullbackProof
import Langlands.AbelianScheme.FieldTheoremOfTheSquareProof

/-! # The `k^(2g)` scaling of the Euler product of an ample line bundle and its inverse -/

universe u

namespace Langlands.AbelianScheme

/-- On a `g`-dimensional abelian variety over an algebraically closed field, let `H` be an
ample line bundle with inverse `N`, let `k ≥ 1`, and let `Nk` be an inverse of `H^{⊗k}`.
Then `χ(H^{⊗k}) · χ(Nk) = k^(2g) · χ(H) · χ(N)`. The published reduction
`ScalingAssembly.algClosedFieldAmpleEulerInverseScalingReduction` is applied to the published
proofs of the balanced cube identity and of the theorem of the square. -/
theorem algClosedFieldAmpleEulerInverseScaling :
    AlgClosedFieldAmpleEulerInverseScalingStatement.{u} :=
  ScalingAssembly.algClosedFieldAmpleEulerInverseScalingReduction
    Langlands.GroupScheme.fieldCubePullback Langlands.GroupScheme.fieldTheoremOfTheSquare

end Langlands.AbelianScheme
