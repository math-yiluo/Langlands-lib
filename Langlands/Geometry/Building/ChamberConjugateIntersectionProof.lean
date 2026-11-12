import Langlands.Geometry.Building.AffineIwahoriTitsInputStatements
import Langlands.Geometry.Building.ChamberParahoricIntersection
import Langlands.Geometry.Building.ChamberIwahoriPrerequisiteReduction
import Langlands.Geometry.Building.PointParahoricCentralizer
import Langlands.Geometry.Building.KPCoverImageReduction
import Langlands.Geometry.Building.KPInducedTorusIwahoriProof
import Langlands.GroupScheme.Rational.RootRankOneFactorizationProof
import Langlands.GroupScheme.Rational.DynamicRootOrderedProductProof
import Langlands.GroupScheme.Rational.SplitTorusCentralizerCocenterAssembly
import Langlands.GroupScheme.Rational.LeviCocenterRootModelProof
import Langlands.GroupScheme.Derived.CocenterQuotientProof
import Langlands.GroupScheme.Derived.SemisimpleProof
import Langlands.GroupScheme.Dynamic.CentralizerReductiveProof
import Langlands.GroupScheme.Reductive.CentralDerivedProductProof
import Langlands.GroupScheme.SimplyConnected.SimplyConnectedFieldExtensionProof
import Langlands.GroupScheme.SimplyConnected.SplitNecessity
import Langlands.GroupScheme.SimplyConnected.SplitCriterion
import Langlands.GroupScheme.SimplyConnected.SplitTorusCentralizerCoverPreimageReduction
import Langlands.GroupScheme.SimplyConnected.SplitTorusCentralizerDerivedAssembly
import Langlands.GroupScheme.SimplyConnected.SplitTorusCentralizerDerivedCorootComparisonProof

/-! # Proof of the chamber-conjugate intersection

KP Theorem 7.5.1, saturation step, on `G(F)^0`: an element of `G(F)` lying in `P_{n C}` for
every `n ∈ N(F) ∩ G(F)^0` lies in `Z(F)^0`. The published conditional theorem
`ParahoricBuildingData.mem_centralizerZero_of_forall_mem_parahoric_normalizerZeroComponent`
is applied with every premise discharged by published proofs, through the cover-image
comparison of KP Corollary 2.6.28 and the centralizer intersection of KP Lemma 7.4.3.
-/

universe u

open Langlands.GroupScheme

namespace Langlands.Geometry.Building

/-- Simple connectedness ascends to an algebraic closure: the case `K = k̄` of the published
`isSimplyConnectedFieldExtension`. -/
theorem isSimplyConnectedAlgebraicClosureAscent :
    IsSimplyConnectedAlgebraicClosureAscentStatement.{u} :=
  fun k _ G hG => isSimplyConnectedFieldExtension k (AlgebraicClosure k) G hG

/-- The derived subgroup of a split-torus centralizer in a simply connected group is simply
connected, from the published structural proofs. -/
theorem splitTorusCentralizerDerivedSimplyConnected :
    SplitTorusCentralizerDerivedSimplyConnectedStatement.{u} :=
  splitTorusCentralizerDerivedSimplyConnected_of_inputs dynamicCentralizerReductive
    derivedSubgroupSemisimple splitSimplyConnectedCorootSpan splitCorootSpanSimplyConnected
    splitTorusCentralizerDerivedCorootComparison isSimplyConnectedAlgebraicClosureAscent

/-- The preimage of a split-torus centralizer in a simply connected cover, from the published
structural proofs. -/
theorem splitTorusCentralizerCoverPreimage :
    SplitTorusCentralizerCoverPreimageStatement.{u} :=
  splitTorusCentralizerCoverPreimage_of_inputs reductiveCentralDerivedProduct
    dynamicCentralizerReductive splitTorusCentralizerDerivedSimplyConnected

/-- Cocenters of split-torus centralizers in simply connected groups are induced tori, from
the published structural proofs. -/
theorem splitTorusCentralizerCocenterInduced :
    SplitTorusCentralizerCocenterInducedStatement.{u} :=
  splitTorusCentralizerCocenterInduced_of_inputs
    ⟨dynamicCentralizerReductive, cocenterQuotientExistence, isSimplyConnectedFieldExtension,
      splitSimplyConnectedCorootSpan, splitTorusCentralizerCocenterRootModel⟩

/-- The cover-image containment `G(F)^♮ ∩ Z(F)^1 ⊆ Z(F)^0` of the proof of KP
Corollary 2.6.28, for every actual zero datum. -/
theorem ZeroSubgroupDatum.coverImageCentralizerNormKernel {F : Type u} [Field F]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {S : CommGroupScheme (AlgebraicGeometry.Spec (CommRingCat.of F))}
    {G Z : GroupScheme (AlgebraicGeometry.Spec (CommRingCat.of F))}
    {i : S.toGrp ⟶ G} {j : Z ⟶ G} (E : ZeroSubgroupDatum i j) :
    E.CoverImageCentralizerNormKernelStatement :=
  E.coverImageCentralizerNormKernel_of_inputs cocenterQuotientExistence
    splitTorusCentralizerCocenterInduced inducedTorusIwahori splitTorusCentralizerCoverPreimage
    isSimplyConnectedFieldExtension

/-- **KP Theorem 7.5.1, saturation step, on `G(F)^0`.** For every chamber `C` of the actual
apartment, an element of `G(F)` lying in `P_{n C}` for every `n ∈ N(F) ∩ G(F)^0` lies in
`Z(F)^0`. -/
theorem chamberConjugateIntersection : ChamberConjugateIntersectionStatement.{u} := by
  intro F _ _ _ _ G _ P hA C hC g hg
  have hrank : RelativeRoot.HasRankOneFactorization P.i :=
    rootRankOneFactorization F G P.isConnectedReductive P.S P.i P.isMaximalSplitTorus
  have hcent : P.CentralizerParahoricIntersectionStatement :=
    P.centralizerParahoricIntersection_of_rankOneFactorization hrank
      P.zeroDatum.coverImageCentralizerNormKernel
  have hdec : P.ChamberIwahoriDecompositionStatement :=
    chamberIwahoriPrerequisiteReduction RelativeRoot.dynamicRootOrderedProduct
      rootRankOneFactorization F G P hcent
  exact P.mem_centralizerZero_of_forall_mem_parahoric_normalizerZeroComponent hA hrank
    RelativeRoot.dynamicRootOrderedProduct hdec hC hg

end Langlands.Geometry.Building
