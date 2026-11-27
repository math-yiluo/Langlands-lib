import Langlands.Representation.Aubert.General.LocalFieldGLRationalFunctorsStatement
import Langlands.Representation.Aubert.GeneralLinearLocalFieldModulusProof
import Mathlib.CategoryTheory.Whiskering

/-! # Transport of the actual normalized GL functors -/

noncomputable section

set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false

universe u v

open CategoryTheory CategoryTheory.Functor AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily.GL

open Langlands.AlgebraicGeometry.PointTopology
open GroupScheme SmoothRep

/-- The normalized block functor comparison for a topological group with a
matched actual parabolic triple: if a continuous group isomorphism
`e : H ≃ₜ* GL_n(F)` carries `P`, `M` and `U` onto the block parabolic, Levi
and radical, then pulling back along `e` and along its Levi restriction
intertwines the normalized functors, by precomposition of functions and by
the identity on vector classes. -/
theorem localFieldGLFunctors_of_subgroupEquiv
    {F : Type u} [Field F] (T : LocalFieldData F) {n : ℕ}
    (B : Langlands.GeneralLinear.BlockShape n)
    {H : Type u} [Group H] [TopologicalSpace H] [LocallyCompactSpace H]
    [NonarchimedeanGroup H] {P M U : Subgroup H}
    (dec : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set H))
    (hmod : Parabolic.LocalFieldGeneralLinearModulusCompatibilityStatement.{u}) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    ∀ (e : H ≃ₜ* Langlands.GeneralLinear n F)
      (_hP : ∀ x, x ∈ P ↔ e x ∈ B.parabolic F)
      (hL : ∀ x, x ∈ M ↔ e x ∈ B.leviSubgroup F)
      (_hR : ∀ x, x ∈ U ↔ e x ∈ B.unipotentSubgroup F),
      let eL := (GroupTransport.subgroupEquiv e hL).trans (B.leviEquivContinuous F).symm
      let iBlock := T.normalizedParabolicInductionFunctor.{u, max (u + 1) v} B
      let rBlock := T.normalizedJacquetFunctor.{u, max (u + 1) v} B
      let iPoint := normalizedInductionFunctor.{u, max (u + 1) v} dec hU
      let rPoint := jacquetFunctor.{u, max (u + 1) v} dec hU
      (∃ α : iBlock ⋙ pullbackFunctor e ≅ pullbackFunctor eL ⋙ iPoint,
        ∀ (A : SmoothRep.{0, u, max (u + 1) v} ℂ (B.Levi F))
          (f : iBlock.obj A) (x : H),
          Induction.eval P (inducingRepresentation dec hU (pullback eL A))
            (SmoothRep.hom (α.app A).hom f) x =
          Induction.eval (B.parabolic F)
            (twist (T.parabolicHalfModulus B) (A.representation.comp (B.leviProjection F)))
            f (e x)) ∧
      (∃ β : rBlock ⋙ pullbackFunctor eL ≅ pullbackFunctor e ⋙ rPoint,
        ∀ (A : SmoothRep.{0, u, max (u + 1) v} ℂ (Langlands.GeneralLinear n F))
          (a : A),
          SmoothRep.hom (β.app A).hom (B.jacquetMk A.representation a) =
            Jacquet.Localization.mk (A.representation.comp e.toMonoidHom) U 1 a) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let := T.generalLinearLocallyCompactSpace n
  let := T.generalLinearNonarchimedean n
  intro e hP hL hR
  have hc := hmod F T n B
  let decB := B.generalSemidirectDecomposition (F := F)
  let hUB := B.isClosed_unipotentSubgroup F
  let block := Parabolic.productToEmbeddedLevi.{u, max (u + 1) v} (F := F) B
  let pullG := pullbackFunctor.{u, u, max (u + 1) v} e
  let pullL := pullbackFunctor.{u, u, max (u + 1) v} (GroupTransport.subgroupEquiv e hL)
  let δ := T.leviModulus B
  have hδ : IsOpen (δ.ker : Set (B.Levi F)) := T.isOpen_ker_leviModulus B
  let αB := B.generalInductionIso.{u, max (u + 1) v} δ hδ hc
  let αe := GroupTransport.inductionIso.{u, max (u + 1) v} decB dec e hP hL hR hUB hU
  let βB := B.generalJacquetIso.{u, max (u + 1) v} δ hδ hc
  let βe := GroupTransport.jacquetIso.{u, max (u + 1) v} decB dec e hL hR hUB hU
  let α := isoWhiskerRight αB.symm pullG ≪≫ isoWhiskerLeft block αe
  let β := isoWhiskerRight βB pullL ≪≫ βe
  constructor
  · refine ⟨α, ?_⟩
    intro A f x
    rfl
  · refine ⟨β, ?_⟩
    intro A a
    rfl

/-- The rational-point and matrix functor comparison follows from the full
upper-block modulus statement, through the standard subgroup comparisons. -/
theorem localFieldGLRationalFunctors_of_modulus
    (hmod : Parabolic.LocalFieldGeneralLinearModulusCompatibilityStatement.{u}) :
    LocalFieldGLRationalFunctorsStatement.{u, v} := by
  intro F _ T n ν hν B
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let G := GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)
  let : TopologicalSpace (RationalPoint F G.X) := pointTopology
  let e := GroupScheme.GeneralLinear.rationalPointsContinuousMulEquiv n F
  let : IsTopologicalGroup (RationalPoint F G.X) :=
    GroupScheme.GeneralLinear.rationalPoints_isTopologicalGroup n F
  let := T.generalLinearLocallyCompactSpace n
  let := T.generalLinearNonarchimedean n
  let : LocallyCompactSpace (RationalPoint F G.X) :=
    e.toHomeomorph.isClosedEmbedding.locallyCompactSpace
  let : NonarchimedeanGroup (RationalPoint F G.X) :=
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
  have hP (x : RationalPoint F G.X) : x ∈ parabolic iD ν J ↔ e x ∈ B.parabolic F :=
    SetLike.ext_iff.mp (parabolic_blockRootSubsetEquiv F ν hν B) x
  have hL (x : RationalPoint F G.X) : x ∈ levi iD ν J ↔ e x ∈ B.leviSubgroup F :=
    SetLike.ext_iff.mp (levi_blockRootSubsetEquiv F ν hν B) x
  have hR (x : RationalPoint F G.X) : x ∈ unipotent iD ν J ↔
      e x ∈ B.unipotentSubgroup F :=
    SetLike.ext_iff.mp (unipotent_blockRootSubsetEquiv F ν hν B) x
  exact localFieldGLFunctors_of_subgroupEquiv T B dec hU hmod e hP hL hR

/-- Actual normalized induction and Jacquet restriction on rational points and
on matrices are naturally isomorphic, over every local field. -/
theorem localFieldGLRationalFunctors : LocalFieldGLRationalFunctorsStatement.{u, v} :=
  localFieldGLRationalFunctors_of_modulus Parabolic.localFieldGeneralLinearModulusCompatibility

end Langlands.Aubert.General.RationalPointFamily.GL
