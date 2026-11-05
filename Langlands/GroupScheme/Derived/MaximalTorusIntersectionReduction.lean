import Langlands.GroupScheme.Derived.MaximalTorusIntersectionStatement
import Langlands.GroupScheme.Absolute.MaximalTorusCentralizerStatement
import Langlands.GroupScheme.Derived.MaximalSplitTorusStatement
import Langlands.GroupScheme.Derived.SmoothnessProof
import Langlands.GroupScheme.Derived.ConnectednessProof
import Langlands.GroupScheme.Derived.FieldBaseChangeAssembly
import Langlands.GroupScheme.Reductive.NormalSubgroup
import Langlands.GroupScheme.Reductive.FieldExtensionProof
import Langlands.GroupScheme.Torus.SelfCentralizingPullback
import Langlands.GroupScheme.Torus.MaximalSelfCentralizing
import Langlands.GroupScheme.Torus.MaximalSplitComparison
import Langlands.GroupScheme.Torus.FiniteGaloisSplittingProof
import Langlands.GroupScheme.Torus.SplitReflection

/-! # Derived-torus intersections from existing structural inputs -/

set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.GroupScheme

/-- An actual derived subgroup of a connected reductive field group is
connected reductive, using smoothness, connectedness and normality. -/
theorem IsDerivedSubgroup.isConnectedReductive
    {k : Type u} [Field k] {G D : GroupScheme (Spec (CommRingCat.of k))}
    {d : D ⟶ G} (hd : IsDerivedSubgroup d) (hG : IsConnectedReductive G) :
    IsConnectedReductive D := by
  let : Smooth G.X.hom := hG.smooth
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : Smooth D.X.hom := derivedSubgroupSmoothness k G D d hd hG.smooth
  let : ConnectedSpace D.X.left :=
    derivedSubgroupConnectedness k G D d hd hG.connectedSpace
  exact hG.of_normalSubgroup d hd.1 hd.isNormal

/-- Over an algebraically closed field, a maximal split torus of the derived
subgroup contained in the ambient torus identifies the full intersection. -/
theorem IsDerivedSubgroup.isTorus_intersection_of_isAlgClosed
    (hself : MaximalTorusCentralizerStatement.{u})
    (hderived : DerivedMaximalSplitTorusStatement.{u})
    {k : Type u} [Field k] [IsAlgClosed k]
    {G D : GroupScheme (Spec (CommRingCat.of k))}
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {d : D ⟶ G} (hd : IsDerivedSubgroup d) (hG : IsConnectedReductive G)
    (t : T.toGrp ⟶ G) (ht : IsMaximalTorus t) :
    IsTorus (subgroupIntersection t d) := by
  have hsplit : ToriAreSplit k := fun A hA =>
    hA.isSplitTorus_of_finiteGaloisSplitting torusFiniteGaloisSplitting
  obtain ⟨A, j, e, hj, _, hcomm⟩ :=
    hderived k G D d hG hd T t (ht.isMaximalSplitTorus (hsplit _ ht.1))
  have hD : IsConnectedReductive D := hd.isConnectedReductive hG
  have hjmax : IsMaximalTorus j := hj.isMaximalTorus hsplit
  have hjself := hself k D hD A j hjmax
  let : IsClosedImmersion d.hom.hom.left := hd.1
  let : Mono d.hom.hom := hd.isRepresentedBy.1
  have hP : IsTorus (subgroupIntersection d t) := by
    have h := isTorus_subgroupIntersection_of_selfCentralizing_of_reflection
      (T := T) (𝟙 D) d t j (CommGroupScheme.groupHom e)
      hjmax.1 ht.2.1 hjmax.2.1
      (by simpa only [Category.id_comp] using hcomm) hjself
      (by simp only [Category.comp_id, SubgroupFunctor.comap_id])
    simpa only [Category.id_comp] using h
  exact IsTorus.of_iso (pullbackSymmetry t d) hP

/-- Two existing structural statements suffice for the full derived-torus
intersection assertion; both remain explicit inputs. -/
def DerivedMaximalTorusIntersectionReductionStatement : Prop :=
  MaximalTorusCentralizerStatement.{u} → DerivedMaximalSplitTorusStatement.{u} →
    DerivedMaximalTorusIntersectionStatement.{u}

/-- Pass to the algebraic closure, identify the full intersection with a
self-centralizing derived torus, and descend the torus property. -/
theorem derivedMaximalTorusIntersection_of_structuralInputs :
    DerivedMaximalTorusIntersectionReductionStatement.{u} := by
  intro hself hderived k _ G D T d t hG hd ht
  let K := AlgebraicClosure k
  let b := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let B := GroupScheme.baseChange b
  let T' := (CommGroupScheme.baseChange b).obj T
  let : IsAffineHom G.X.hom := hG.isAffineHom
  have hG' : IsConnectedReductive (B.obj G) :=
    connectedReductiveFieldExtensionStatement k K G hG
  have hd' : IsDerivedSubgroup (B.map d) :=
    hd.baseChange_of_eq b (derivedSubgroup_baseChange_eq_of_field b G)
  have ht' : IsMaximalTorus (T := T') (B.map t) :=
    isMaximalTorus_baseChange_of_torusCentralizer_eq K ht.1 ht.2.1
      (hself k G hG T t ht)
  have hI : IsTorus (subgroupIntersection (B.map t) (B.map d)) :=
    IsDerivedSubgroup.isTorus_intersection_of_isAlgClosed
      (k := K) (G := B.obj G) (D := B.obj D) (T := T') (d := B.map d)
      hself hderived hd' hG' (B.map t) ht'
  apply IsTorus.of_baseChange (K := K)
  exact IsTorus.of_iso (subgroupIntersectionBaseChangeIso b t d) hI

end Langlands.GroupScheme
