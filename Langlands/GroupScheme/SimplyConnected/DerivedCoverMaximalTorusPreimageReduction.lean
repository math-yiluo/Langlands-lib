import Langlands.GroupScheme.SimplyConnected.DerivedCoverMaximalTorusPreimageStatement
import Langlands.GroupScheme.Absolute.MaximalTorusCentralizerStatement
import Langlands.GroupScheme.Derived.MaximalSplitTorusStatement
import Langlands.GroupScheme.Derived.FieldBaseChangeAssembly
import Langlands.GroupScheme.Reductive.FieldExtensionProof
import Langlands.GroupScheme.CentralIsogeny.BaseChange
import Langlands.GroupScheme.CentralIsogeny.SplitMaximalTorusLiftProof
import Langlands.GroupScheme.Torus.MaximalSelfCentralizing
import Langlands.GroupScheme.Torus.MaximalSplitComparison
import Langlands.GroupScheme.Torus.FiniteGaloisSplittingProof
import Langlands.GroupScheme.Torus.SplitReflection
import Langlands.GroupScheme.CentralIsogeny.TorusCentralizerReflection
import Langlands.GroupScheme.Torus.SelfCentralizingPullback

/-! # Reduction of full derived-cover torus preimages to structural inputs -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Over an algebraically closed field, the derived maximal-split-torus
statement supplies a maximal source torus mapping into the ambient maximal
torus through a central isogeny. -/
theorem exists_maximalTorus_lift_into_ambient_of_isAlgClosed
    (hderived : DerivedMaximalSplitTorusStatement.{u})
    {k : Type u} [Field k] [IsAlgClosed k]
    {H D C : GroupScheme (Spec (CommRingCat.of k))}
    (hH : IsConnectedReductive H) (hD : IsConnectedReductive D)
    (hC : IsConnectedReductive C)
    (d : D ⟶ H) (π : C ⟶ D) (hd : IsDerivedSubgroup d)
    (hπ : IsCentralIsogeny π)
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    (i : T.toGrp ⟶ H) (hi : IsMaximalTorus i) :
    ∃ (A : CommGroupScheme (Spec (CommRingCat.of k)))
      (j : A.toGrp ⟶ C) (f : A.toGrp ⟶ T.toGrp),
      IsMaximalTorus j ∧ j ≫ π ≫ d = f ≫ i := by
  have hsplit : ToriAreSplit k := fun A hA =>
    hA.isSplitTorus_of_finiteGaloisSplitting torusFiniteGaloisSplitting
  obtain ⟨S, s, e, hs, _, hsd⟩ :=
    hderived k H D d hH hd T i (hi.isMaximalSplitTorus (hsplit _ hi.1))
  obtain ⟨A, j, f, _, hj, hjπ⟩ :=
    centralIsogenySplitMaximalTorusLift k C D hC hD π hπ S s hs.1.1
      (hs.isMaximalTorus hsplit)
  refine ⟨A, j, CommGroupScheme.groupHom f ≫ CommGroupScheme.groupHom e, hj, ?_⟩
  rw [← Category.assoc, hjπ, Category.assoc, hsd, ← Category.assoc]

/-- After extension to an algebraically closed field, two explicit structural
statements supply a closed self-centralizing source torus inside the full
ambient torus preimage. -/
theorem exists_selfCentralizing_sourceTorus_after_fieldExtension
    (hself : MaximalTorusCentralizerStatement.{u})
    (hderived : DerivedMaximalSplitTorusStatement.{u})
    {k K : Type u} [Field k] [Field K] [Algebra k K] [IsAlgClosed K]
    {H D C : GroupScheme (Spec (CommRingCat.of k))}
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {d : D ⟶ H} {π : C ⟶ D} {i : T.toGrp ⟶ H}
    (h : IsSimplyConnectedDerivedCover d π) (hi : IsMaximalTorus i) :
    let b := Spec.map (CommRingCat.ofHom (algebraMap k K))
    let B := GroupScheme.baseChange b
    let T' := (CommGroupScheme.baseChange b).obj T
    ∃ (A : CommGroupScheme (Spec (CommRingCat.of K)))
      (j : A.toGrp ⟶ B.obj C) (f : A.toGrp ⟶ T'.toGrp),
      IsTorus A.toGrp ∧ IsClosedSubgroup j ∧
      torusCentralizer j = SubgroupFunctor.range j ∧
      j ≫ B.map π ≫ B.map d = f ≫ B.map i := by
  let b := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let B := GroupScheme.baseChange b
  let T' := (CommGroupScheme.baseChange b).obj T
  have hH := connectedReductiveFieldExtensionStatement k K H h.isConnectedReductive
  have hD := connectedReductiveFieldExtensionStatement k K D
    h.isSimplyConnectedCover.isSemisimple.isConnectedReductive
  have hC := connectedReductiveFieldExtensionStatement k K C
    h.isSimplyConnectedCover.isSimplyConnected.isSemisimple.isConnectedReductive
  have : IsAffineHom H.X.hom := h.isConnectedReductive.isAffineHom
  have hd : IsDerivedSubgroup (B.map d) :=
    h.isDerivedSubgroup.baseChange_of_eq b (derivedSubgroup_baseChange_eq_of_field b H)
  have hπ : IsCentralIsogeny (B.map π) := h.isSimplyConnectedCover.isCentralIsogeny.baseChange b
  have hi' : IsMaximalTorus (T := T') (B.map i) :=
    isMaximalTorus_baseChange_of_torusCentralizer_eq K hi.1 hi.2.1
      (hself k H h.isConnectedReductive T i hi)
  obtain ⟨A, j, f, hj, hfac⟩ :=
    exists_maximalTorus_lift_into_ambient_of_isAlgClosed (T := T') hderived hH hD hC
      (B.map d) (B.map π) hd hπ (B.map i) hi'
  exact ⟨A, j, f, hj.1, hj.2.1, hself K (B.obj C) hC A j hj, hfac⟩

/-- The full derived-cover preimage assertion follows from the two displayed
structural statements, which remain explicit hypotheses. -/
def DerivedCoverMaximalTorusPreimageReductionStatement : Prop :=
  MaximalTorusCentralizerStatement.{u} → DerivedMaximalSplitTorusStatement.{u} →
    DerivedCoverMaximalTorusPreimageStatement.{u}

/-- Identify the full preimage with a source torus after algebraic closure,
then descend the torus property to the original field. -/
theorem derivedCoverMaximalTorusPreimage_of_structuralInputs :
    DerivedCoverMaximalTorusPreimageReductionStatement.{u} := by
  intro hself hderived k _ H D C T d π i h hi
  let K := AlgebraicClosure k
  let b := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let B := GroupScheme.baseChange b
  let T' := (CommGroupScheme.baseChange b).obj T
  obtain ⟨A, j, f, hA, hj, hjself, hcomm⟩ :=
    exists_selfCentralizing_sourceTorus_after_fieldExtension (K := K) hself hderived h hi
  have hπ : IsCentralIsogeny (B.map π) :=
    h.isSimplyConnectedCover.isCentralIsogeny.baseChange b
  have : IsClosedImmersion (B.map d).hom.hom.left :=
    h.isDerivedSubgroup.1.baseChange b
  have : Mono (B.map d).hom.hom := Over.mono_of_mono_left _
  have hP : IsTorus (subgroupIntersection (B.map π ≫ B.map d) (B.map i)) :=
    isTorus_subgroupIntersection_of_selfCentralizing_of_reflection
      (T := T') (B.map π) (B.map d) (B.map i) j f hA
      (hi.2.1.baseChange b) hj hcomm hjself (hπ.torusCentralizer_comap hA j)
  apply IsTorus.of_baseChange (K := K)
  apply IsTorus.of_iso (subgroupIntersectionBaseChangeIso b (π ≫ d) i)
  simpa only [Functor.map_comp] using hP

end Langlands.GroupScheme
