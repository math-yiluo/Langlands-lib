import Langlands.GroupScheme.Derived.MaximalTorusIntersectionReduction
import Langlands.GroupScheme.Rational.GeometricSubgroupTorus
import Langlands.GroupScheme.Torus.MaximalBaseChangeProof
import Langlands.GroupScheme.Absolute.MaximalTorusCentralizerFromQuotient
import Langlands.GroupScheme.Dynamic.CentralizerReductiveProof
import Langlands.GroupScheme.Absolute.SolvableTorusQuotientProof

/-! # The full intersection of a maximal torus with the actual derived subgroup -/

set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Over every field, the entire scheme-theoretic intersection of a maximal
torus with the actual derived subgroup of a connected reductive group is a torus. -/
theorem derivedMaximalTorusIntersection :
    DerivedMaximalTorusIntersectionStatement.{u} := by
  intro k _ G D T d t hG hd ht
  let K := AlgebraicClosure k
  let b := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let B := GroupScheme.baseChange b
  let T' := (CommGroupScheme.baseChange b).obj T
  let : Smooth G.X.hom := hG.smooth
  let : IsAffineHom G.X.hom := hG.isAffineHom
  have hG' : IsConnectedReductive (B.obj G) :=
    connectedReductiveFieldExtensionStatement k K G hG
  have hd' : IsDerivedSubgroup (B.map d) :=
    hd.baseChange_of_eq b (derivedSubgroup_baseChange_eq_of_field b G)
  have ht' : IsMaximalTorus (T := T') (B.map t) :=
    (maximalTorusBaseChange k K G T t ht.1 ht.2.1).mp ht
  let : Smooth (B.obj G).X.hom := hG'.smooth
  let : IsAffineHom (B.obj G).X.hom := hG'.isAffineHom
  let : ConnectedSpace (B.obj G).X.left := hG'.connectedSpace
  obtain ⟨A, j, e, _, hjmax, _, hcomm⟩ :=
    hd'.exists_compatible_maximalTorus_of_isAlgClosed (T := T') (B.map t) ht'
  have hD' : IsConnectedReductive (B.obj D) := hd'.isConnectedReductive hG'
  have hjself := algClosedMaximalTorusCentralizer_fromQuotient
    dynamicCentralizerReductive solvableTorusQuotient K (B.obj D) hD' A j hjmax
  let : IsClosedImmersion (B.map d).hom.hom.left := hd'.1
  let : Mono (B.map d).hom.hom := hd'.isRepresentedBy.1
  have hP : IsTorus (subgroupIntersection (B.map d) (B.map t)) := by
    have h := isTorus_subgroupIntersection_of_selfCentralizing_of_reflection
      (T := T') (𝟙 (B.obj D)) (B.map d) (B.map t) j (CommGroupScheme.groupHom e)
      hjmax.1 ht'.2.1 hjmax.2.1
      (by simpa only [Category.id_comp] using hcomm.symm) hjself
      (by simp only [Category.comp_id, SubgroupFunctor.comap_id])
    simpa only [Category.id_comp] using h
  have hI : IsTorus (subgroupIntersection (B.map t) (B.map d)) :=
    IsTorus.of_iso (pullbackSymmetry (B.map t) (B.map d)) hP
  apply IsTorus.of_baseChange (K := K)
  exact IsTorus.of_iso (subgroupIntersectionBaseChangeIso b t d) hI

end Langlands.GroupScheme
