import Langlands.GroupScheme.CommutativeSubgroupIntersectionComparison
import Langlands.GroupScheme.Absolute.MaximalRankRadicalTorusIntersectionStatement
import Langlands.GroupScheme.Absolute.AlgebraicClosureBaseChange
import Langlands.GroupScheme.Absolute.BorelContainingSubgroupConnectedStatement
import Langlands.GroupScheme.Torus.MaximalBaseChangeStatement

/-! # Canonical intersections with a supplied geometric solvable radical -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
variable {P R : GroupScheme (Spec (CommRingCat.of k))}
  {T : CommGroupScheme (Spec (CommRingCat.of k))}

/-- The canonical commutative intersection with a supplied solvable radical.
This construction alone does not assert that the intersection is a torus. -/
def solvableRadicalTorusIntersection (f : T.toGrp ⟶ P) (r : R ⟶ P)
    (hr : IsSolvableRadical r) : CommGroupScheme (Spec (CommRingCat.of k)) := by
  let : IsClosedImmersion r.hom.hom.left := hr.isClosedSubgroup
  let : Mono r.hom.hom := Over.mono_of_mono_left _
  exact commutativeSubgroupIntersection f r

/-- The actual projection to the specified commutative subgroup. -/
abbrev solvableRadicalTorusIntersectionFst (f : T.toGrp ⟶ P) (r : R ⟶ P)
    (hr : IsSolvableRadical r) :
    (solvableRadicalTorusIntersection f r hr).toGrp ⟶ T.toGrp :=
  subgroupIntersectionFst f r

/-- The actual projection to the supplied radical representative. -/
abbrev solvableRadicalTorusIntersectionSnd (f : T.toGrp ⟶ P) (r : R ⟶ P)
    (hr : IsSolvableRadical r) :
    (solvableRadicalTorusIntersection f r hr).toGrp ⟶ R :=
  subgroupIntersectionSnd f r

/-- The canonical projections have the same actual ambient composite. -/
theorem solvableRadicalTorusIntersection_condition
    (f : T.toGrp ⟶ P) (r : R ⟶ P) (hr : IsSolvableRadical r) :
    solvableRadicalTorusIntersectionFst f r hr ≫ f =
      solvableRadicalTorusIntersectionSnd f r hr ≫ r :=
  subgroupIntersection_condition f r

/-- The common image is the entire intersection on every test scheme. -/
theorem range_solvableRadicalTorusIntersection
    (f : T.toGrp ⟶ P) (r : R ⟶ P) (hr : IsSolvableRadical r) :
    SubgroupFunctor.range (solvableRadicalTorusIntersectionFst f r hr ≫ f) =
      SubgroupFunctor.range f ⊓ SubgroupFunctor.range r :=
  range_subgroupIntersectionHom f r

/-- The projection to the commutative subgroup is closed without a torus premise. -/
theorem isClosedSubgroup_solvableRadicalTorusIntersectionFst
    (f : T.toGrp ⟶ P) (r : R ⟶ P) (hr : IsSolvableRadical r) :
    IsClosedSubgroup (solvableRadicalTorusIntersectionFst f r hr) := by
  change IsClosedImmersion (subgroupIntersectionFst f r).hom.hom.left
  exact MorphismProperty.of_isPullback
    (subgroupIntersection_isPullback_scheme f r).flip hr.isClosedSubgroup

/-- The maximum-rank intersection statement and forward maximal-torus base change
imply maximality for the canonical intersection of a supplied geometric radical.
Geometric connectedness of the subgroup remains an explicit hypothesis. -/
theorem isMaximalTorus_solvableRadicalTorusIntersectionSnd_of_geometric
    (hintersection : MaximalRankRadicalTorusIntersectionStatement.{u})
    (hbase : MaximalTorusBaseChangeStatement.{u})
    {G : GroupScheme (Spec (CommRingCat.of k))}
    (hG : IsConnectedReductive G) (j : P ⟶ G)
    (hj : IsClosedSubgroup j) (hP : Smooth P.X.hom)
    (hconnected : ConnectedSpace
      ((GroupScheme.baseChange (toAlgebraicClosure k)).obj P).X.left)
    (t : T.toGrp ⟶ G) (ht : IsMaximalTorus t)
    (f : T.toGrp ⟶ P) (hfactor : f ≫ j = t)
    (r : R ⟶ P) (hr : IsGeometricSolvableRadical r) :
    IsMaximalTorus (solvableRadicalTorusIntersectionSnd f r hr.1) := by
  let : Smooth G.X.hom := hG.smooth
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : Smooth P.X.hom := hP
  let : IsClosedImmersion r.hom.hom.left := hr.1.isClosedSubgroup
  let : Mono r.hom.hom := Over.mono_of_mono_left _
  let bc := GroupScheme.baseChange (toAlgebraicClosure k)
  let Tbar := (CommGroupScheme.baseChange (toAlgebraicClosure k)).obj T
  have htbar : IsMaximalTorus (T := Tbar) (bc.map t) :=
    (hbase k (AlgebraicClosure k) G T t ht.1 ht.2.1).mp ht
  have hPbar : Smooth (bc.obj P).X.hom := by
    change Smooth (pullback.snd P.X.hom (toAlgebraicClosure k))
    infer_instance
  have hfactorbar : bc.map f ≫ bc.map j = bc.map t := by
    rw [← bc.map_comp, hfactor]
  obtain ⟨Sbar, sTbar, sRbar, hsTbar, hsRbar, hcompbar, hrangebar⟩ :=
    hintersection (AlgebraicClosure k) (bc.obj G)
      hG.baseChange_toAlgebraicClosure (bc.obj P) (bc.map j)
      (hj.baseChange _) hPbar hconnected Tbar (bc.map t) htbar
      (bc.map f) hfactorbar (bc.obj R) (bc.map r) hr.2
  have hf : IsClosedSubgroup f :=
    IsClosedSubgroup.of_comp hj (by rw [hfactor]; exact ht.2.1)
  change IsMaximalTorus
    (T := commutativeSubgroupIntersection f r)
    (commutativeSubgroupIntersectionSnd f r)
  exact isMaximalTorus_commutativeSubgroupIntersectionSnd_of_baseChange_representative
    (K := AlgebraicClosure k) f r sTbar sRbar hf hr.1.isClosedSubgroup
    hsTbar hsRbar hcompbar hrangebar

/-- For a parabolic, the Borel-containing connectedness statement supplies the
geometric connectedness needed by the preceding descent theorem. All three
unproved structural inputs and the supplied geometric radical remain explicit. -/
theorem IsParabolicSubgroup.exists_radicalTorusIntersection_of_structural_inputs
    (hintersection : MaximalRankRadicalTorusIntersectionStatement.{u})
    (hbase : MaximalTorusBaseChangeStatement.{u})
    (hconnected : BorelContainingSubgroupConnectedStatement.{u})
    {G : GroupScheme (Spec (CommRingCat.of k))}
    (hG : IsConnectedReductive G) (j : P ⟶ G) (hj : IsParabolicSubgroup j)
    (t : T.toGrp ⟶ G) (ht : IsMaximalTorus t)
    (f : T.toGrp ⟶ P) (hfactor : f ≫ j = t)
    (r : R ⟶ P) (hr : IsGeometricSolvableRadical r) :
    ∃ (S : CommGroupScheme (Spec (CommRingCat.of k)))
      (sT : S.toGrp ⟶ T.toGrp) (sR : S.toGrp ⟶ R),
      IsClosedSubgroup sT ∧ IsMaximalTorus sR ∧
      sT ≫ f = sR ≫ r ∧
      SubgroupFunctor.range (sT ≫ f) =
        SubgroupFunctor.range f ⊓ SubgroupFunctor.range r := by
  let bc := GroupScheme.baseChange (toAlgebraicClosure k)
  have hGbar : IsConnectedReductive (bc.obj G) := hG.baseChange_toAlgebraicClosure
  let : Smooth (bc.obj G).X.hom := hGbar.smooth
  let : IsAffineHom (bc.obj G).X.hom := hGbar.isAffineHom
  let : ConnectedSpace (bc.obj G).X.left := hGbar.connectedSpace
  let : Smooth P.X.hom := hj.smooth
  have hPbar : Smooth (bc.obj P).X.hom := by
    change Smooth (pullback.snd P.X.hom (toAlgebraicClosure k))
    infer_instance
  obtain ⟨B, jB, fB, hjB, hfB⟩ := hj.exists_isBorelSubgroup
  have hPconnected : ConnectedSpace (bc.obj P).X.left :=
    hconnected (AlgebraicClosure k) (bc.obj G) (bc.obj P) B
      (bc.map j) jB fB (hj.isClosedSubgroup.baseChange _) hPbar hjB hfB
  refine ⟨solvableRadicalTorusIntersection f r hr.1,
    solvableRadicalTorusIntersectionFst f r hr.1,
    solvableRadicalTorusIntersectionSnd f r hr.1,
    isClosedSubgroup_solvableRadicalTorusIntersectionFst f r hr.1, ?_,
    solvableRadicalTorusIntersection_condition f r hr.1,
    range_solvableRadicalTorusIntersection f r hr.1⟩
  exact isMaximalTorus_solvableRadicalTorusIntersectionSnd_of_geometric
    hintersection hbase hG j hj.isClosedSubgroup hj.smooth hPconnected
    t ht f hfactor r hr

end Langlands.GroupScheme
