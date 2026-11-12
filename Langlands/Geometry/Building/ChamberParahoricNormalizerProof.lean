import Langlands.Geometry.Building.AffineIwahoriTitsInputStatements
import Langlands.Geometry.Building.PointParahoricNormalizer
import Langlands.Geometry.Building.KPCoverImageReduction
import Langlands.Geometry.Building.KPInducedTorusIwahoriProof
import Langlands.GroupScheme.Rational.RootRankOneFactorizationProof
import Langlands.GroupScheme.Rational.SplitTorusCentralizerCocenterAssembly
import Langlands.GroupScheme.Rational.LeviCocenterRootModelProof
import Langlands.GroupScheme.Derived.CocenterQuotientProof
import Langlands.GroupScheme.Derived.SemisimpleProof
import Langlands.GroupScheme.Dynamic.CentralizerReductiveProof
import Langlands.GroupScheme.Reductive.CentralDerivedProductProof
import Langlands.GroupScheme.Reductive.RootDatumExistence
import Langlands.GroupScheme.SimplyConnected.SplitNecessity
import Langlands.GroupScheme.SimplyConnected.SplitCriterion
import Langlands.GroupScheme.SimplyConnected.SimplyConnectedFieldExtensionProof
import Langlands.GroupScheme.SimplyConnected.FieldExtensionStructuralAssembly
import Langlands.GroupScheme.SimplyConnected.SplitCoverExistenceProof
import Langlands.GroupScheme.SimplyConnected.UniversalPropertyProof
import Langlands.GroupScheme.SimplyConnected.SplitTorusCentralizerDerivedAssembly
import Langlands.GroupScheme.SimplyConnected.SplitTorusCentralizerDerivedCorootComparisonProof
import Langlands.GroupScheme.SimplyConnected.SplitTorusCentralizerCoverPreimageReduction
import Langlands.GroupScheme.Descent.TensorFullCoverProof
import Langlands.GroupScheme.Torus.MaximalBaseChangeProof

/-! # The chamber parahoric–normalizer intersection (KP Lemma 7.5.2(1))

Proof of `ChamberParahoricNormalizerStatement`: for the actual data under the apartment
axioms and a chamber `C`, every `n ∈ N(F)` lying in `P_C` lies in `Z(F)^0`. The proof
applies the published chamber intersection
`ParahoricBuildingData.zeroNormalizer_eq_map_centralizerZero_of_isChamber` and discharges
both of its algebraic inputs with published proofs: relative-root rank-one factorization
(`rootRankOneFactorization`) and the cover-image containment of KP Corollary 2.6.28
(`ZeroSubgroupDatum.coverImageCentralizerNormKernel_of_inputs`, whose structural inputs
are all proved in the Library).
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme

namespace Langlands.Geometry.Building

/-- **KP Lemma 7.5.2(1)**, `I ∩ N = Z`: for the actual data under the apartment axioms and a
chamber `C`, every `n ∈ N(F)` lying in `P_C` lies in `Z(F)^0`. -/
theorem chamberParahoricNormalizer : ChamberParahoricNormalizerStatement.{u} := by
  -- In a simply connected group, derived subgroups of split-torus centralizers are simply
  -- connected.
  have hG : SplitTorusCentralizerDerivedSimplyConnectedStatement.{u} :=
    splitTorusCentralizerDerivedSimplyConnected_of_inputs dynamicCentralizerReductive
      derivedSubgroupSemisimple splitSimplyConnectedCorootSpan splitCorootSpanSimplyConnected
      splitTorusCentralizerDerivedCorootComparison
      (isSimplyConnectedAlgebraicClosureAscent_of_descent_and_splitStructure
        simplyConnectedCoverTensorDescent splitSimplyConnectedCoverExistence
        simplyConnectedCentralCoverUniversalProperty maximalTorusBaseChange rootDatumExistence
        splitSimplyConnectedCorootSpan splitCorootSpanSimplyConnected)
  -- The preimage of a split-torus centralizer in a simply connected cover.
  have hPL : SplitTorusCentralizerCoverPreimageStatement.{u} :=
    splitTorusCentralizerCoverPreimage_of_inputs reductiveCentralDerivedProduct
      dynamicCentralizerReductive hG
  -- The cocenter of a split-torus centralizer in a simply connected group is induced.
  have hF : SplitTorusCentralizerCocenterInducedStatement.{u} :=
    splitTorusCentralizerCocenterInduced_of_inputs
      ⟨dynamicCentralizerReductive, cocenterQuotientExistence, isSimplyConnectedFieldExtension,
        splitSimplyConnectedCorootSpan, splitTorusCentralizerCocenterRootModel⟩
  intro F _ _ _ _ G _ P hP C hC n hn
  -- `G(F)^♮ ∩ Z(F)^1 ⊆ Z(F)^0` for the actual zero datum (KP Corollary 2.6.28).
  have hZ : P.zeroDatum.CoverImageCentralizerNormKernelStatement :=
    P.zeroDatum.coverImageCentralizerNormKernel_of_inputs cocenterQuotientExistence hF
      inducedTorusIwahori hPL isSimplyConnectedFieldExtension
  -- Rank-one factorization for the actual maximal split torus of `P`.
  have hrank : RelativeRoot.HasRankOneFactorization P.i :=
    rootRankOneFactorization F G P.isConnectedReductive P.S P.i P.isMaximalSplitTorus
  apply (P.mem_normalizerZero_iff (n := n)).mpr
  rw [← P.zeroNormalizer_eq_map_centralizerZero_of_isChamber hP hrank hZ hC]
  exact ⟨n.property, hn⟩

end Langlands.Geometry.Building
