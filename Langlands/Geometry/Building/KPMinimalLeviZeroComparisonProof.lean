import Langlands.Geometry.Building.KPCoverImageReduction
import Langlands.Geometry.Building.KPInducedTorusIwahoriProof
import Langlands.GroupScheme.Derived.CocenterQuotientProof
import Langlands.GroupScheme.Derived.MaximalTorusProductSurjectivityProof
import Langlands.GroupScheme.Dynamic.CentralizerReductiveProof
import Langlands.GroupScheme.Rational.SplitTorusCentralizerCocenterAssembly
import Langlands.GroupScheme.Rational.LeviCocenterRootModelProof
import Langlands.GroupScheme.Rational.LeviCocenterRootModelReduction
import Langlands.GroupScheme.Reductive.CentralDerivedProductProof
import Langlands.GroupScheme.Reductive.RootDatumExistence
import Langlands.GroupScheme.Reductive.SplitExistence
import Langlands.GroupScheme.Reductive.SplitCentralIsogenyExistenceProof
import Langlands.GroupScheme.Reductive.SplitSemisimplicity
import Langlands.GroupScheme.SimplyConnected.FieldExtensionStructuralAssembly
import Langlands.GroupScheme.SimplyConnected.SplitNecessityAssembly
import Langlands.GroupScheme.SimplyConnected.SplitCoverExistenceProof
import Langlands.GroupScheme.SimplyConnected.UniversalPropertyProof
import Langlands.GroupScheme.SimplyConnected.SplitCriterion
import Langlands.GroupScheme.SimplyConnected.SplitTorusCentralizerDerivedAssembly
import Langlands.GroupScheme.SimplyConnected.SplitTorusCentralizerDerivedCorootComparisonProof
import Langlands.GroupScheme.SimplyConnected.SplitTorusCentralizerCoverPreimageReduction
import Langlands.GroupScheme.Descent.TensorFullCoverProof
import Langlands.GroupScheme.Torus.MaximalBaseChangeProof

/-! # KP Lemma 2.6.27 and Corollary 2.6.28 for the actual minimal-Levi zero subgroup -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme

namespace Langlands.Geometry.Building.ZeroSubgroupDatum

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G Z : GroupScheme (Spec (CommRingCat.of F))}
  {i : S.toGrp ⟶ G} {j : Z ⟶ G} (E : ZeroSubgroupDatum i j)

/-- **KP Lemma 2.6.27 and Corollary 2.6.28** for every actual zero datum `E` over a
nonarchimedean local field: if `G` is simply connected then `Z(F)^0 = Z(F)^1`, and in general
`G(F)^0 ∩ Z(F)^1 = Z(F)^0`. The structural inputs of the conditional assembly
`minimalLeviZeroComparison_of_inputs` are all discharged by published Library proofs. -/
theorem minimalLeviZeroComparison : E.MinimalLeviZeroComparisonStatement := by
  -- Integral coroot generation for simply connected split groups (Milne 23.59, necessity).
  have hspan : SplitSimplyConnectedCorootSpanStatement.{u} :=
    splitSimplyConnectedCorootSpan_of_inputs
      ⟨splitReductiveExistence, splitCentralIsogenyExistence, splitSemisimpleRootDatum⟩
  -- Simple connectedness ascends along field extensions (CGP A.4.11(1)).
  have hsc : IsSimplyConnectedFieldExtensionStatement.{u} :=
    isSimplyConnectedFieldExtension_of_descent_and_splitStructure
      simplyConnectedCoverTensorDescent splitSimplyConnectedCoverExistence
      simplyConnectedCentralCoverUniversalProperty maximalTorusBaseChange rootDatumExistence
      hspan splitCorootSpanSimplyConnected
  -- The cocenter of a split-torus centralizer in a simply connected group is induced.
  have hF : SplitTorusCentralizerCocenterInducedStatement.{u} :=
    splitTorusCentralizerCocenterInduced_of_inputs
      ⟨dynamicCentralizerReductive, cocenterQuotientExistence, hsc, hspan,
        splitTorusCentralizerCocenterRootModel⟩
  -- The derived subgroup of such a centralizer is simply connected.
  have hG : SplitTorusCentralizerDerivedSimplyConnectedStatement.{u} :=
    splitTorusCentralizerDerivedSimplyConnected_of_inputs dynamicCentralizerReductive
      (derivedSubgroupSemisimple_of_rootDatum_product rootDatumExistence
        derivedMaximalTorusProductSurjectivity)
      hspan splitCorootSpanSimplyConnected splitTorusCentralizerDerivedCorootComparison
      (isSimplyConnectedAlgebraicClosureAscent_of_descent_and_splitStructure
        simplyConnectedCoverTensorDescent splitSimplyConnectedCoverExistence
        simplyConnectedCentralCoverUniversalProperty maximalTorusBaseChange rootDatumExistence
        hspan splitCorootSpanSimplyConnected)
  -- The preimage of a split-torus centralizer in a simply connected central cover.
  have hPL : SplitTorusCentralizerCoverPreimageStatement.{u} :=
    splitTorusCentralizerCoverPreimage_of_inputs reductiveCentralDerivedProduct
      dynamicCentralizerReductive hG
  exact E.minimalLeviZeroComparison_of_inputs cocenterQuotientExistence hF hG
    inducedTorusIwahori hPL hsc

end Langlands.Geometry.Building.ZeroSubgroupDatum
