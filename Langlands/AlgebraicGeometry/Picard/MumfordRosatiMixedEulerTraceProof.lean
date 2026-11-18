import Langlands.AlgebraicGeometry.Picard.MumfordRosatiMixedEulerTraceCharZeroReduction
import Langlands.AlgebraicGeometry.Picard.MumfordRosatiEulerDegreeProof
import Langlands.AbelianScheme.IsogenyDegreeTateDeterminantCharZeroReduction
import Langlands.AbelianScheme.IsogenyDegreeTateDeterminantNormReduction
import Langlands.AbelianScheme.EndomorphismDegreeLinePolynomialProof
import Langlands.AbelianScheme.IsogenyFinrankKernelCardProof
import Langlands.AbelianScheme.IsogenyKernelCardTateDeterminantProof
import Langlands.AbelianScheme.TateDeterminantNonzeroSurjectiveProof
import Langlands.AbelianScheme.FieldSurjectiveEndomorphismIsogenyProof

/-! # The Mumford Rosati mixed Euler trace formula

The exact target `MumfordMixedEulerTraceStatement` follows by composing three published
reductions with six published input theorems.
-/

universe u

namespace Langlands.AbelianScheme.Rosati

/-- The Mumford Rosati mixed Euler trace formula, in its full universe scope. -/
theorem mumfordMixedEulerTrace : MumfordMixedEulerTraceStatement.{u} :=
  mumfordMixedEulerTraceCharZeroReduction
    (isogenyDegreeTateDeterminantCharZeroReduction endomorphismDegreeLinePolynomial
      (isogenyDegreeTateDeterminantNormReduction isogenyFinrankKernelCard
        isogenyKernelCardTateDeterminant tateDeterminantNonzeroSurjective
        fieldSurjectiveEndomorphismIsogeny))
    mumfordEulerDegree

end Langlands.AbelianScheme.Rosati
