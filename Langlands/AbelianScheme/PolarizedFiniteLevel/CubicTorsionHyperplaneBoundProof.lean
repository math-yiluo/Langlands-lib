import Langlands.AbelianScheme.PolarizedFiniteLevel.CubicTorsionHyperplaneBoundAssembly
import Langlands.AbelianScheme.FieldSymmetricMultiplicationPullbackProof
import Langlands.AlgebraicGeometry.Picard.AlgClosedFieldAmpleEulerInverseScalingProof
import Langlands.AlgebraicGeometry.Picard.AlgClosedFieldEulerInverseSymmetryProof
import Langlands.AbelianScheme.PolarizedFiniteLevel.CubicFibreCohomologyProof

/-! # Proof of the torsion-hyperplane bound for a supplied canonical cubic embedding -/

universe u

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

/-- For a supplied nondegenerate closed embedding by the canonical cubic bundle
of a polarized datum over an algebraically closed field, every hyperplane
contains at most `6^g*d*g!*n^(2*g-2)` of the `n`-torsion points. -/
theorem cubicTorsionHyperplaneBound : CubicTorsionHyperplaneBoundStatement.{u} :=
  cubicTorsionHyperplaneBoundReduction Langlands.GroupScheme.fieldSymmetricMultiplicationPullback
    algClosedFieldAmpleEulerInverseScaling algClosedFieldEulerInverseSymmetry
    cubicFibreCohomology

end Langlands.AbelianScheme.PolarizedFiniteLevel
