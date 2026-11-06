import Langlands.GroupScheme.SimplyConnected.DerivedCoverMaximalTorusPreimageStatement
import Langlands.GroupScheme.Absolute.MaximalTorusCentralizerProof
import Langlands.GroupScheme.Rational.GeometricSubgroupTorus
import Langlands.GroupScheme.Derived.FieldBaseChangeAssembly
import Langlands.GroupScheme.Reductive.FieldExtensionProof
import Langlands.GroupScheme.CentralIsogeny.BaseChange
import Langlands.GroupScheme.CentralIsogeny.SplitMaximalTorusLiftProof
import Langlands.GroupScheme.Torus.MaximalSelfCentralizing
import Langlands.GroupScheme.Torus.SplitReflection
import Langlands.GroupScheme.CentralIsogeny.TorusCentralizerReflection
import Langlands.GroupScheme.Torus.SelfCentralizingPullback

/-! # The full maximal-torus preimage in a simply connected derived cover -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Over every field, the full scheme-theoretic preimage of a maximal torus
in a simply connected derived cover is a torus. -/
theorem derivedCoverMaximalTorusPreimage :
    DerivedCoverMaximalTorusPreimageStatement.{u} := by
  intro k _ H D C T d π i h hi
  let K := AlgebraicClosure k
  let b := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let B := GroupScheme.baseChange b
  let T' := (CommGroupScheme.baseChange b).obj T
  have hH : IsConnectedReductive (B.obj H) :=
    connectedReductiveFieldExtensionStatement k K H h.isConnectedReductive
  have hD : IsConnectedReductive (B.obj D) :=
    connectedReductiveFieldExtensionStatement k K D
      h.isSimplyConnectedCover.isSemisimple.isConnectedReductive
  have hC : IsConnectedReductive (B.obj C) :=
    connectedReductiveFieldExtensionStatement k K C
      h.isSimplyConnectedCover.isSimplyConnected.isSemisimple.isConnectedReductive
  let : IsAffineHom H.X.hom := h.isConnectedReductive.isAffineHom
  have hd : IsDerivedSubgroup (B.map d) :=
    h.isDerivedSubgroup.baseChange_of_eq b (derivedSubgroup_baseChange_eq_of_field b H)
  have hπ : IsCentralIsogeny (B.map π) :=
    h.isSimplyConnectedCover.isCentralIsogeny.baseChange b
  have hi' : IsMaximalTorus (T := T') (B.map i) :=
    isMaximalTorus_baseChange_of_torusCentralizer_eq K hi.1 hi.2.1
      (maximalTorusCentralizer k H h.isConnectedReductive T i hi)
  let : Smooth (B.obj H).X.hom := hH.smooth
  let : IsAffineHom (B.obj H).X.hom := hH.isAffineHom
  let : ConnectedSpace (B.obj H).X.left := hH.connectedSpace
  obtain ⟨S, s, e, hS, hs, _, he⟩ :=
    hd.exists_compatible_maximalTorus_of_isAlgClosed (T := T') (B.map i) hi'
  obtain ⟨A, j, f, _, hj, hjπ⟩ :=
    centralIsogenySplitMaximalTorusLift K (B.obj C) (B.obj D) hC hD
      (B.map π) hπ S s hS hs
  have hcomm : j ≫ B.map π ≫ B.map d =
      (CommGroupScheme.groupHom f ≫ CommGroupScheme.groupHom e) ≫ B.map i := by
    rw [← Category.assoc, hjπ, Category.assoc, ← he]
    exact (Category.assoc _ _ _).symm
  let : IsClosedImmersion (B.map d).hom.hom.left := hd.1
  let : Mono (B.map d).hom.hom := hd.isRepresentedBy.1
  have hP : IsTorus (subgroupIntersection (B.map π ≫ B.map d) (B.map i)) :=
    isTorus_subgroupIntersection_of_selfCentralizing_of_reflection
      (T := T') (B.map π) (B.map d) (B.map i) j
      (CommGroupScheme.groupHom f ≫ CommGroupScheme.groupHom e)
      hj.1 hi'.2.1 hj.2.1 hcomm
      (maximalTorusCentralizer K (B.obj C) hC A j hj)
      (hπ.torusCentralizer_comap hj.1 j)
  apply IsTorus.of_baseChange (K := K)
  apply IsTorus.of_iso (subgroupIntersectionBaseChangeIso b (π ≫ d) i)
  simpa only [Functor.map_comp] using hP

end Langlands.GroupScheme
