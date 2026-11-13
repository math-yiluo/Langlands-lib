import Langlands.Representation.Aubert.General.GeneralLinearRationalComparisonStatement
import Langlands.Representation.Aubert.General.GeneralLinearRationalIndexing
import Langlands.Representation.Aubert.General.OperatorTransport
import Langlands.Representation.Aubert.General.RationalUnipotentRegularity
import Langlands.Representation.Aubert.GeneralLinearModulusCompatibilityProof
import Langlands.Representation.Aubert.GeneralLinearSpecialization

/-! # Proof of the rational-point/matrix comparison of the GL operator -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily.GL

open GroupScheme
open Langlands.AlgebraicGeometry.PointTopology
open SmoothRep
open Langlands.GeneralLinear (BlockShape)

section Membership

variable (k : Type u) [Field k] {N : ℕ}
  (ν : cocharacterLattice
    (splitTorus.commGroupScheme (Spec (CommRingCat.of k)) (ULift (Fin N))))
  (hν : StrictAnti (GroupScheme.GeneralLinear.cocharacterCoordEquiv (Fin N) k ν))

local notation "iD" => GroupScheme.GeneralLinear.diagonalTorus (Fin N) (CommRingCat.of k)

/-- The block shape attached to a simple-root subset, read through the inverse
edge equivalence, is the inverse block-root equivalence. -/
theorem leviRootSubsetEquiv_symm_edge (J : Finset (SimpleRoot iD ν)) :
    (BlockShape.leviRootSubsetEquiv N).symm ((edgeSimpleRootEquiv k ν hν).symm.finsetCongr J) =
      (blockRootSubsetEquiv k ν hν).symm J :=
  rfl

theorem mem_parabolic_iff_block (J : Finset (SimpleRoot iD ν))
    (x : RationalPoint k (GroupScheme.GeneralLinear.groupScheme (Fin N) (CommRingCat.of k)).X) :
    x ∈ parabolic iD ν J ↔
      GroupScheme.GeneralLinear.rationalPointsEquiv N (CommRingCat.of k) x ∈
        ((blockRootSubsetEquiv k ν hν).symm J).parabolic k := by
  obtain ⟨B, rfl⟩ := (blockRootSubsetEquiv k ν hν).surjective J
  rw [Equiv.symm_apply_apply]
  exact SetLike.ext_iff.mp (parabolic_blockRootSubsetEquiv k ν hν B) x

theorem mem_levi_iff_block (J : Finset (SimpleRoot iD ν))
    (x : RationalPoint k (GroupScheme.GeneralLinear.groupScheme (Fin N) (CommRingCat.of k)).X) :
    x ∈ levi iD ν J ↔
      GroupScheme.GeneralLinear.rationalPointsEquiv N (CommRingCat.of k) x ∈
        ((blockRootSubsetEquiv k ν hν).symm J).leviSubgroup k := by
  obtain ⟨B, rfl⟩ := (blockRootSubsetEquiv k ν hν).surjective J
  rw [Equiv.symm_apply_apply]
  exact SetLike.ext_iff.mp (levi_blockRootSubsetEquiv k ν hν B) x

theorem mem_unipotent_iff_block (J : Finset (SimpleRoot iD ν))
    (x : RationalPoint k (GroupScheme.GeneralLinear.groupScheme (Fin N) (CommRingCat.of k)).X) :
    x ∈ unipotent iD ν J ↔
      GroupScheme.GeneralLinear.rationalPointsEquiv N (CommRingCat.of k) x ∈
        ((blockRootSubsetEquiv k ν hν).symm J).unipotentSubgroup k := by
  obtain ⟨B, rfl⟩ := (blockRootSubsetEquiv k ν hν).surjective J
  rw [Equiv.symm_apply_apply]
  exact SetLike.ext_iff.mp (unipotent_blockRootSubsetEquiv k ν hν B) x

end Membership

theorem rationalAlternatingOperatorComparison :
    RationalAlternatingOperatorComparisonStatement.{u, v} := by
  intro p _ F T N ν hν
  let := T.topology
  let : IsTopologicalRing F.Carrier := by
    let := T.valuativeRel
    let := T.localField
    infer_instance
  let : TopologicalSpace (RationalPoint F.Carrier
      (GroupScheme.GeneralLinear.groupScheme (Fin N) (CommRingCat.of F.Carrier)).X) :=
    pointTopology
  let e := GroupScheme.GeneralLinear.rationalPointsContinuousMulEquiv N F.Carrier
  let σ := (edgeSimpleRootEquiv F.Carrier ν hν).symm
  let Bs := fun J => (blockRootSubsetEquiv F.Carrier ν hν).symm J
  let : T2Space F.Carrier := T.fieldT2
  let : LocallyCompactSpace (GeneralLinear N F.Carrier) := T.generalLinearLocallyCompactSpace N
  let : NonarchimedeanGroup (GeneralLinear N F.Carrier) := T.generalLinearNonarchimedean N
  let : IsTopologicalGroup (RationalPoint F.Carrier
      (GroupScheme.GeneralLinear.groupScheme (Fin N) (CommRingCat.of F.Carrier)).X) :=
    GroupScheme.GeneralLinear.rationalPoints_isTopologicalGroup N F.Carrier
  refine ⟨⟨e.toHomeomorph.isClosedEmbedding.locallyCompactSpace,
    NonarchimedeanGroup.nonarchimedean_of_emb e.symm.toMonoidHom
      e.symm.toHomeomorph.isOpenEmbedding,
    e.toHomeomorph.isEmbedding.t2Space⟩, ?_⟩
  intro instLC instNA instT2 iD hgen hG hi dec
  have hc : ∀ B : BlockShape N, Parabolic.GeneralLinearModulusCompatibility F T B :=
    fun B => Parabolic.generalLinearModulusCompatibility F T B
  have hflG := fun B : BlockShape N =>
    Parabolic.generalLinearParabolicFiniteLength.{u, max (u + 1) v} F T B (hc B)
  have hPP : ∀ J x, x ∈ parabolic iD ν J ↔ e x ∈ (Bs J).parabolic F.Carrier :=
    fun J x => mem_parabolic_iff_block F.Carrier ν hν J x
  have hMM : ∀ J x, x ∈ levi iD ν J ↔ e x ∈ (Bs J).leviSubgroup F.Carrier :=
    fun J x => mem_levi_iff_block F.Carrier ν hν J x
  have hUU : ∀ J x, x ∈ unipotent iD ν J ↔ e x ∈ (Bs J).unipotentSubgroup F.Carrier :=
    fun J x => mem_unipotent_iff_block F.Carrier ν hν J x
  have hUG : ∀ J, IsClosed ((Bs J).unipotentSubgroup F.Carrier :
      Set (GeneralLinear N F.Carrier)) :=
    fun J => (Bs J).isClosed_unipotentSubgroup F.Carrier
  have hU₀ : ∀ J, IsClosed (unipotent iD ν J : Set (RationalPoint F.Carrier
      (GroupScheme.GeneralLinear.groupScheme (Fin N) (CommRingCat.of F.Carrier)).X)) := by
    intro J
    have hset : (unipotent iD ν J : Set (RationalPoint F.Carrier
        (GroupScheme.GeneralLinear.groupScheme (Fin N) (CommRingCat.of F.Carrier)).X)) =
        e ⁻¹' ((Bs J).unipotentSubgroup F.Carrier : Set (GeneralLinear N F.Carrier)) :=
      Set.ext (hUU J)
    rw [hset]
    exact (hUG J).preimage e.continuous
  have hP₀ : ∀ J, IsClosed (parabolic iD ν J : Set (RationalPoint F.Carrier
      (GroupScheme.GeneralLinear.groupScheme (Fin N) (CommRingCat.of F.Carrier)).X)) := by
    intro J
    have hset : (parabolic iD ν J : Set (RationalPoint F.Carrier
        (GroupScheme.GeneralLinear.groupScheme (Fin N) (CommRingCat.of F.Carrier)).X)) =
        e ⁻¹' ((Bs J).parabolic F.Carrier : Set (GeneralLinear N F.Carrier)) :=
      Set.ext (hPP J)
    rw [hset]
    exact ((Bs J).isClosed_parabolic F.Carrier).preimage e.continuous
  have hproj₀ : ∀ J, Continuous (dec J).projection := by
    intro J
    refine GroupTransport.continuous_projection_transport
      (Bs J).generalSemidirectDecomposition (dec J) e (hPP J) (hMM J) (hUU J) ?_
    have hfun : ⇑((Bs J).generalSemidirectDecomposition (F := F.Carrier)).projection =
        fun g => (Bs J).leviEquivContinuous F.Carrier
          ((Bs J).leviProjectionContinuous F.Carrier g) :=
      funext ((Bs J).generalSemidirectDecomposition_projection)
    rw [hfun]
    exact ((Bs J).leviEquivContinuous F.Carrier).continuous.comp
      ((Bs J).leviProjectionContinuous F.Carrier).continuous
  have hUc₀ : ∀ J, Jacquet.Localization.IsLimitOfCompactSubgroups (unipotent iD ν J) := by
    let := T.valuativeRel
    let := T.localField
    exact fun J => standardUnipotent_isLimitOfCompactSubgroups_of_standardCocharacterStatement
      iD ν standardCocharacter.{u} hG hi hgen J
  have hiFl₀ : ∀ J, PreservesFiniteLength
      (normalizedInductionFunctor.{u, max (u + 1) v} (dec J) (hU₀ J)) := fun J =>
    GroupTransport.inductionPreservesFiniteLength_transport
      (Bs J).generalSemidirectDecomposition (dec J) e (hPP J) (hMM J) (hUU J) (hUG J) (hU₀ J)
      (hflG (Bs J)).1
  have hrFl₀ : ∀ J, PreservesFiniteLength
      (jacquetFunctor.{u, max (u + 1) v} (dec J) (hU₀ J)) := fun J =>
    GroupTransport.jacquetPreservesFiniteLength_transport
      (Bs J).generalSemidirectDecomposition (dec J) e (hMM J) (hUU J) (hUG J) (hU₀ J)
      (hflG (Bs J)).2.2.1
  refine ⟨⟨hU₀, hP₀, hproj₀, hUc₀, hiFl₀, hrFl₀⟩, ?_⟩
  intro hU hP hproj hUc hiFl hrFl
  have hGL := Aubert.generalAlternatingOperator_eq.{u, max (u + 1) v} F T N hc
  rw [← hGL]
  let := simpleRelativeRootFintype iD
    (GroupScheme.GeneralLinear.hasRelativeRootSystem_diagonalTorus (n := Fin N) F.Carrier)
    hi.isSplitSubtorus.1 ν
  exact GroupTransport.alternatingOperator_transport _ _ _ _ _ _ _ _ _ _ _ _ e σ
    hPP hMM hUU

end Langlands.Aubert.General.RationalPointFamily.GL
