import Langlands.Representation.Aubert.General.CanonicalRationalOperator
import Langlands.Representation.Aubert.General.GeneralLinearRationalIndexing
import Langlands.Representation.Aubert.General.GroupTransport
import Langlands.Group.GL.AlgebraicPointTopology
import Langlands.GroupScheme.Rational.GeneralLinearProof
import Langlands.GroupScheme.Reductive.GeneralLinear
import Langlands.AllField.Group.GL.CompactOpen
import Langlands.AllField.Representation.Induction.Parabolic
import Langlands.AllField.Representation.Jacquet.Parabolic

/-! # Actual rational-point and matrix GL functors over any local field -/

noncomputable section

set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency.types false

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily.GL

open Langlands.AlgebraicGeometry.PointTopology
open GroupScheme SmoothRep

section Components

variable {F : Type u} [Field F] (T : LocalFieldData F) {n : ℕ}
  (B : Langlands.GeneralLinear.BlockShape n)

variable {H : Type u} [Group H] [TopologicalSpace H] [LocallyCompactSpace H]
  [NonarchimedeanGroup H] {P M U : Subgroup H}
  (dec : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set H))

private def inductionTransport :
    letI := T.topology
    (H ≃ₜ* Langlands.GeneralLinear n F) → (M ≃ₜ* B.Levi F) → Prop :=
  letI := T.topology
  fun e eL =>
    let iBlock := T.normalizedParabolicInductionFunctor.{u, max (u + 1) v} B
    let iPoint := normalizedInductionFunctor.{u, max (u + 1) v} dec hU
    ∃ α : iBlock ⋙ pullbackFunctor e ≅ pullbackFunctor eL ⋙ iPoint,
      ∀ (A : SmoothRep.{0, u, max (u + 1) v} ℂ (B.Levi F))
        (f : iBlock.obj A) (x : H),
        Induction.eval P (inducingRepresentation dec hU (pullback eL A))
          (SmoothRep.hom (α.app A).hom f) x =
        Induction.eval (B.parabolic F)
          (twist (T.parabolicHalfModulus B) (A.representation.comp (B.leviProjection F)))
          f (e x)

private def jacquetTransport :
    letI := T.topology
    (H ≃ₜ* Langlands.GeneralLinear n F) → (M ≃ₜ* B.Levi F) → Prop :=
  letI := T.topology
  fun e eL =>
    let rBlock := T.normalizedJacquetFunctor.{u, max (u + 1) v} B
    let rPoint := jacquetFunctor.{u, max (u + 1) v} dec hU
    ∃ β : rBlock ⋙ pullbackFunctor eL ≅ pullbackFunctor e ⋙ rPoint,
      ∀ (A : SmoothRep.{0, u, max (u + 1) v} ℂ (Langlands.GeneralLinear n F))
        (a : A),
        SmoothRep.hom (β.app A).hom (B.jacquetMk A.representation a) =
        Jacquet.Localization.mk (A.representation.comp e.toMonoidHom) U 1 a

end Components

/-- Transport from the matrix ambient group and its block product Levi
intertwines actual normalized induction and Jacquet restriction. The induction
comparison is precomposition of functions, and the Jacquet comparison sends
each vector class to the class of the same vector. -/
def LocalFieldGLRationalFunctorsStatement : Prop :=
  ∀ (F : Type u) [Field F] (T : LocalFieldData F) (n : ℕ)
    (ν : cocharacterLattice
      (splitTorus.commGroupScheme (Spec (CommRingCat.of F)) (ULift (Fin n))))
    (hν : StrictAnti (GroupScheme.GeneralLinear.cocharacterCoordEquiv (Fin n) F ν))
    (B : Langlands.GeneralLinear.BlockShape n),
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
    let iD := GroupScheme.GeneralLinear.diagonalTorus (Fin n) (CommRingCat.of F)
    let hG := isConnectedReductive_generalLinear F (Fin n)
    let hi := GroupScheme.GeneralLinear.isMaximalSplitTorus_diagonalTorus (n := Fin n) F
    let hgen := (GroupScheme.GeneralLinear.isGenericCocharacter_diagonalTorus_iff F ν).mpr
      hν.injective
    let J := blockRootSubsetEquiv F ν hν B
    let dec := isSemidirectDecomposition_of_standardCocharacterStatement iD ν
      standardCocharacter.{u} hG hi hgen J
    let hU := canonicalStandardUnipotent_isClosed hG iD ν hi hgen J
    let eL := (GroupTransport.subgroupEquiv e
      (fun x => SetLike.ext_iff.mp (levi_blockRootSubsetEquiv F ν hν B) x)).trans
        (B.leviEquivContinuous F).symm
    inductionTransport.{u, v} T B dec hU e eL ∧
      jacquetTransport.{u, v} T B dec hU e eL

end Langlands.Aubert.General.RationalPointFamily.GL
