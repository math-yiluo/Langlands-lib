import Langlands.Representation.Aubert.General.LocalFieldGLRationalOperatorStatement

/-! The actual rational-point Aubert operator specialized to general linear groups. -/

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily.GL

open Langlands.AlgebraicGeometry.PointTopology
open GroupScheme SmoothRep

universe u v

/-- Each actual GL standard Levi has the exactness and finite-length
properties needed for the rational-point operator. The rational-point and
matrix operators agree under exact Grothendieck pullback in every rank. -/
def LocalFieldGLRationalOperatorRealizationStatement : Prop :=
  ∀ (F : Type u) [Field F] (T : LocalFieldData F) (n : ℕ)
    (ν : cocharacterLattice
      (splitTorus.commGroupScheme (Spec (CommRingCat.of F)) (ULift (Fin n))))
    (hν : StrictAnti (GroupScheme.GeneralLinear.cocharacterCoordEquiv (Fin n) F ν)),
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := T.fieldT2
    let G := GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)
    letI : TopologicalSpace (RationalPoint F G.X) := pointTopology
    let e := GroupScheme.GeneralLinear.rationalPointsContinuousMulEquiv n F
    letI : IsTopologicalGroup (RationalPoint F G.X) :=
      GroupScheme.GeneralLinear.rationalPoints_isTopologicalGroup n F
    letI := T.generalLinearLocallyCompactSpace n
    letI := T.generalLinearNonarchimedean n
    letI : LocallyCompactSpace (RationalPoint F G.X) :=
      e.toHomeomorph.isClosedEmbedding.locallyCompactSpace
    letI : NonarchimedeanGroup (RationalPoint F G.X) :=
      NonarchimedeanGroup.nonarchimedean_of_emb e.symm.toMonoidHom
        e.symm.toHomeomorph.isOpenEmbedding
    letI : T2Space (RationalPoint F G.X) := e.toHomeomorph.isEmbedding.t2Space
    let iD := GroupScheme.GeneralLinear.diagonalTorus (Fin n) (CommRingCat.of F)
    let hG := isConnectedReductive_generalLinear F (Fin n)
    let hi := GroupScheme.GeneralLinear.isMaximalSplitTorus_diagonalTorus (n := Fin n) F
    let hgen := (GroupScheme.GeneralLinear.isGenericCocharacter_diagonalTorus_iff F ν).mpr
      hν.injective
    letI := simpleRelativeRootFintype iD
      (relativeRootSystem F G hG _ iD hi) hi.isSplitSubtorus.1 ν
    let dec := isSemidirectDecomposition_of_standardCocharacterStatement iD ν
      standardCocharacter.{u} hG hi hgen
    let hU := canonicalStandardUnipotent_isClosed hG iD ν hi hgen
    let p := FiniteLengthGrothendieckGroup.pullback.{u,u,max (u + 1) v} e
    LocalFieldMatrixParabolicExactLength.{u,v} T n ∧
      (∀ J, ParabolicFiniteLength.{u,max (u + 1) v} (dec J) (hU J)) ∧
      ∀ (hRat : ∀ J, ParabolicFiniteLength.{u,max (u + 1) v} (dec J) (hU J))
        (hMat : LocalFieldMatrixParabolicExactLength.{u,v} T n),
        p.comp (localFieldMatrixAlternatingOperator T n hMat) =
          (alternatingOperator.{u,u,max (u + 1) v}
            (parabolic iD ν) (levi iD ν) (unipotent iD ν) dec hU hRat).comp p

end Langlands.Aubert.General.RationalPointFamily.GL
