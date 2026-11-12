import Langlands.AlgebraicGeometry.AlgebraicSpace.ReducedClosedSubspaceProof
import Langlands.AlgebraicGeometry.AlgebraicSpace.QuasiAffineSourceAFNoetherianSchemeApproximationProof

/-! # Proof of AF representability from a finite surjection with quasi-affine source

Gross, Proposition 3.5, specialized to a finite surjection with quasi-affine source over an
affine base: the Noetherian case (by Noetherian induction, from the reduced closed subspace
statement) combined with Noetherian approximation.
-/

universe u

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

/-- A finite surjective image of a quasi-affine scheme over `Spec R` is represented by an AF
scheme. -/
theorem finiteSurjectiveQuasiAffineSourceAF : FiniteSurjectiveQuasiAffineSourceAFStatement.{u} :=
  quasiAffineSourceAFNoetherianSchemeApproximation
    (noetherianSchemeQuasiAffineSourceAF_of_reducedClosedSubspace
      ReducedClosedSubspace.reducedClosedSubspace)

end Langlands.AlgebraicGeometry.AlgebraicSpace
