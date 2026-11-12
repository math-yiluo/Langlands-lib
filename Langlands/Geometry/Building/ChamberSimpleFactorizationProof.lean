import Langlands.Geometry.Building.ChamberSimpleFactorizationPrerequisiteReduction
import Langlands.Geometry.Building.KPCoverImageReduction
import Langlands.Geometry.Building.KPInducedTorusIwahoriProof
import Langlands.GroupScheme.Rational.RootRankOneFactorizationProof
import Langlands.GroupScheme.Rational.SplitTorusCentralizerCocenterAssembly
import Langlands.GroupScheme.Rational.LeviCocenterRootModelProof
import Langlands.GroupScheme.Derived.CocenterQuotientProof
import Langlands.GroupScheme.Derived.SemisimpleProof
import Langlands.GroupScheme.Dynamic.CentralizerReductiveProof
import Langlands.GroupScheme.Reductive.CentralDerivedProductProof
import Langlands.GroupScheme.SimplyConnected.SimplyConnectedFieldExtensionProof
import Langlands.GroupScheme.SimplyConnected.SplitNecessity
import Langlands.GroupScheme.SimplyConnected.SplitCriterion
import Langlands.GroupScheme.SimplyConnected.SplitTorusCentralizerDerivedAssembly
import Langlands.GroupScheme.SimplyConnected.SplitTorusCentralizerDerivedCorootComparisonProof
import Langlands.GroupScheme.SimplyConnected.SplitTorusCentralizerCoverPreimageReduction

/-!
# Proof of the chamber-simple factorization (KP (7.5.1))

`chamberSimpleFactorization` proves `ChamberSimpleFactorizationStatement`. It applies the
published reduction `chamberSimpleFactorizationPrerequisiteReduction` to the published proof
`rootRankOneFactorization` and to the cover-image comparison
`G(F)^♮ ∩ Z(F)^1 ⊆ Z(F)^0` for every zero datum. The comparison comes from the published
conditional theorem `ZeroSubgroupDatum.coverImageCentralizerNormKernel_of_inputs`, whose
structural inputs are assembled here from published proofs.
-/

universe u

open Langlands.GroupScheme

namespace Langlands.Geometry.Building

/-- KP (7.5.1), `I ⊆ s I s U_ψ`: for the actual data under the apartment axioms, a chamber `C`,
a chamber-simple affine root `ψ` with derivative the root `a` and a coroot of `ψ`, every element
of `P_C` is a product `b' u` with `b' ∈ P_{r C}` and `u ∈ U_ψ`. -/
theorem chamberSimpleFactorization : ChamberSimpleFactorizationStatement.{u} := by
  -- Simple connectedness ascends to an algebraic closure.
  have hascent : IsSimplyConnectedAlgebraicClosureAscentStatement.{u} :=
    isSimplyConnectedAlgebraicClosureAscent_of_descent_and_splitStructure
      simplyConnectedCoverTensorDescent splitSimplyConnectedCoverExistence
      simplyConnectedCentralCoverUniversalProperty maximalTorusBaseChange rootDatumExistence
      splitSimplyConnectedCorootSpan splitCorootSpanSimplyConnected
  -- Derived subgroups of split-torus centralizers in simply connected groups.
  have hderived : SplitTorusCentralizerDerivedSimplyConnectedStatement.{u} :=
    splitTorusCentralizerDerivedSimplyConnected_of_inputs dynamicCentralizerReductive
      derivedSubgroupSemisimple splitSimplyConnectedCorootSpan splitCorootSpanSimplyConnected
      splitTorusCentralizerDerivedCorootComparison hascent
  -- Preimages of split-torus centralizers in a simply connected cover.
  have hPL : SplitTorusCentralizerCoverPreimageStatement.{u} :=
    splitTorusCentralizerCoverPreimage_of_inputs reductiveCentralDerivedProduct
      dynamicCentralizerReductive hderived
  -- Cocenters of split-torus centralizers in simply connected groups are induced.
  have hF : SplitTorusCentralizerCocenterInducedStatement.{u} :=
    splitTorusCentralizerCocenterInduced_of_inputs
      ⟨dynamicCentralizerReductive, cocenterQuotientExistence, isSimplyConnectedFieldExtension,
        splitSimplyConnectedCorootSpan, splitTorusCentralizerCocenterRootModel⟩
  exact chamberSimpleFactorizationPrerequisiteReduction rootRankOneFactorization
    fun _ _ _ _ _ _ _ P => P.zeroDatum.coverImageCentralizerNormKernel_of_inputs
      cocenterQuotientExistence hF inducedTorusIwahori hPL isSimplyConnectedFieldExtension

end Langlands.Geometry.Building
