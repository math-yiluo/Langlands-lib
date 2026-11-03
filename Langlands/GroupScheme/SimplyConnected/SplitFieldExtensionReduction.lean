import Langlands.GroupScheme.SimplyConnected.GeometricReduction
import Langlands.GroupScheme.SimplyConnected.SplitCriterionStatement
import Langlands.GroupScheme.SimplyConnected.SplitNecessityStatement
import Langlands.GroupScheme.Reductive.RootDatumStatement
import Langlands.GroupScheme.Reductive.RootDatumBaseChangeProof
import Langlands.GroupScheme.Torus.ExistenceProof
import Langlands.GroupScheme.Torus.SplitReflection
import Langlands.GroupScheme.Torus.MaximalBaseChangeStatement

/-! # Simple-connectedness ascent for groups with split maximal tori -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- With the two coroot criteria, root-datum existence, maximality preservation,
and semisimplicity preservation, a simply connected group with a split maximal
torus stays simply connected under every field extension. -/
theorem IsSimplyConnected.fieldExtension_of_splitMaximalTorus
    (hsemi : IsSemisimpleFieldExtensionStatement.{u})
    (hmax : MaximalTorusBaseChangeStatement.{u})
    (hex : RootDatumExistenceStatement.{u})
    (hnec : SplitSimplyConnectedCorootSpanStatement.{u})
    (hsuff : SplitCorootSpanSimplyConnectedStatement.{u})
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    {G : GroupScheme (Spec (CommRingCat.of k))} (hG : IsSimplyConnected G)
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (hT : IsSplitTorus T.toGrp)
    (i : T.toGrp ⟶ G) (hi : IsMaximalTorus i) :
    IsSimplyConnected
      ((GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj G) := by
  have := hG.isSemisimple.isConnectedReductive.isAffineHom
  have := hG.isSemisimple.isConnectedReductive.smooth
  let b := Spec.map (CommRingCat.ofHom (algebraMap k K))
  have hGK := hsemi k K G hG.isSemisimple
  have := hGK.isConnectedReductive.isAffineHom
  obtain ⟨J, _, P, hP, hPred⟩ :=
    hex k G hG.isSemisimple.isConnectedReductive T hT i hi
  have hspan := hnec k G hG T hT i hi J P hP hPred
  have hiK := (hmax k K G T i hi.1 hi.2.1).mp hi
  apply hsuff K ((GroupScheme.baseChange b).obj G) hGK
    ((CommGroupScheme.baseChange b).obj T) (hT.baseChange b)
    ((GroupScheme.baseChange b).map i) hiK J (SplitRootDatum.baseChange b T hT P)
  · exact hP.baseChange G T hT i
  · exact (SplitRootDatum.corootSpan_eq_top_iff b T hT P).mpr hspan

set_option linter.defProp false in
/-- The coroot criteria give the geometric extension step between algebraically
closed fields, assuming root-datum existence, maximality preservation, finite
Galois splitting of tori, and semisimplicity preservation. -/
def isSimplyConnectedAlgClosedFieldExtension_of_corootCriterion
    (hsemi : IsSemisimpleFieldExtensionStatement.{u})
    (hmax : MaximalTorusBaseChangeStatement.{u})
    (hex : RootDatumExistenceStatement.{u})
    (hnec : SplitSimplyConnectedCorootSpanStatement.{u})
    (hsuff : SplitCorootSpanSimplyConnectedStatement.{u})
    (hsplit : TorusFiniteGaloisSplittingStatement.{u}) :
    IsSimplyConnectedAlgClosedFieldExtensionStatement.{u} := by
  intro k K _ _ _ _ _ G hG
  have := hG.isSemisimple.isConnectedReductive.isAffineHom
  have := hG.isSemisimple.isConnectedReductive.smooth
  obtain ⟨T, i, hi⟩ := maximalTorusExistence k G
  exact hG.fieldExtension_of_splitMaximalTorus hsemi hmax hex hnec hsuff T
    (hi.1.isSplitTorus_of_finiteGaloisSplitting hsplit) i hi

/-- After the algebraic-closure ascent input is proved, the split coroot
argument supplies the other geometric input and hence arbitrary field-extension
ascent. All still-unproved structural statements remain explicit hypotheses. -/
theorem isSimplyConnectedFieldExtension_of_algebraicClosureAscent_and_corootCriterion
    (hsemi : IsSemisimpleFieldExtensionStatement.{u})
    (hcentral : CentralIsogenyBaseChangeStatement.{u})
    (hmax : MaximalTorusBaseChangeStatement.{u})
    (hex : RootDatumExistenceStatement.{u})
    (hnec : SplitSimplyConnectedCorootSpanStatement.{u})
    (hsuff : SplitCorootSpanSimplyConnectedStatement.{u})
    (hsplit : TorusFiniteGaloisSplittingStatement.{u})
    (hascent : IsSimplyConnectedAlgebraicClosureAscentStatement.{u}) :
    IsSimplyConnectedFieldExtensionStatement.{u} :=
  isSimplyConnectedFieldExtension_of_geometricInputs hsemi hcentral
    ⟨hascent, isSimplyConnectedAlgClosedFieldExtension_of_corootCriterion
      hsemi hmax hex hnec hsuff hsplit⟩

end Langlands.GroupScheme
