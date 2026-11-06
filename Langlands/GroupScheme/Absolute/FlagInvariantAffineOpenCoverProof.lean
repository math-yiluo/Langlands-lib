import Langlands.GroupScheme.Absolute.FlagInvariantAffineOpenCoverReduction
import Langlands.GroupScheme.Absolute.BorelProperQuotientProof
import Langlands.GroupScheme.Absolute.BorelConjugacyProof
import Langlands.GroupScheme.Absolute.MaximalTorusConjugacyProof
import Langlands.GroupScheme.FlagCoreAssembly
import Langlands.GroupScheme.SolvableProperFixedPointProof
import Langlands.GroupScheme.SpanningLineStabilizerProof
import Langlands.GroupScheme.Torus.FiniteGaloisSplittingProof

/-! # Invariant affine neighbourhoods in actual Borel quotients -/

universe u

namespace Langlands.GroupScheme

/-- Let `G` be a smooth connected affine group over an algebraically closed field, `T` a
maximal torus, and `U` a smooth connected unipotent closed subgroup contained in every Borel
subgroup through `T`. For every Borel quotient `q : G ⟶ Q` with its left translation action
`a`, every rational point of `Q` lies in an affine open subset of `Q` invariant under the
restriction of `a` to `U`. -/
theorem flagInvariantAffineOpenCover : FlagInvariantAffineOpenCoverStatement.{u} :=
  flagInvariantAffineOpenCover_of_prerequisites
    (FlagCore.flagCoreDualLine_of_prerequisites someBorelQuotientProper borelConjugacy
      maximalTorusConjugacy torusFiniteGaloisSplitting solvableProperFixedPoint)
    spanningLineStabilizer someBorelQuotientProper borelConjugacy

end Langlands.GroupScheme
