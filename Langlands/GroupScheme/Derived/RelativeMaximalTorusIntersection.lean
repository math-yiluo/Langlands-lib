import Langlands.GroupScheme.Derived.TorusQuotientCommutators
import Langlands.GroupScheme.Derived.SemisimplePerfectProof
import Langlands.GroupScheme.Derived.Functoriality
import Langlands.GroupScheme.Reductive.RelativeDerivedReduction
import Langlands.GroupScheme.Reductive.TitsKernelTorus
import Langlands.GroupScheme.Torus.CommutativeReductive
import Langlands.GroupScheme.Torus.NormalIntersectionSmooth
import Langlands.GroupScheme.Torus.RelativeReductive

/-! # Relative maximal tori intersect the derived group in relative maximal tori -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

namespace Langlands.GroupScheme

/-- A closed perfect subgroup containing every commutator is the full
scheme-theoretic derived subgroup. -/
theorem isDerivedSubgroup_of_perfect_of_containsCommutators
    {S : Scheme.{u}} {G D : GroupScheme S} (d : D ⟶ G)
    (hd : IsClosedSubgroup d) (hD : derivedSubgroup D = ⊤)
    (hcomm : (SubgroupFunctor.range d).ContainsCommutators) : IsDerivedSubgroup d := by
  refine ⟨hd, le_antisymm ?_ (derivedSubgroup_le_range d hd hcomm)⟩
  intro U x hx
  obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
  apply mem_derivedSubgroup_comp d
  rw [hD]
  exact Subgroup.mem_top _

/-- A closed relative semisimple subgroup with relative-torus quotient is
exactly the derived subgroup at every actual field-valued point of the base. -/
theorem isDerivedSubgroup_fieldFiber_of_semisimple_torusQuotient
    {S : Scheme.{u}} {G D Q : GroupScheme S} (d : D ⟶ G)
    (hd : IsClosedSubgroup d) (hD : IsReductive D)
    (hss : ∀ s : S, IsSemisimple (geometricFiber D s))
    (q : G ⟶ Q) (hQ : RelativeTorus.IsTorus Q)
    (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range d) q)
    {k : Type u} [Field k] (b : Spec (CommRingCat.of k) ⟶ S) :
    IsDerivedSubgroup ((baseChange b).map d) :=
  isDerivedSubgroup_of_perfect_of_containsCommutators _ (hd.baseChange b)
    (semisimplePerfect k _ (hD.isSemisimple_baseChange hss b))
    (hq.containsCommutators_range_baseChange_of_isTorus hQ b)

section Intersection

variable {S : Scheme.{u}} {G D Q : GroupScheme S} {T : CommGroupScheme S}
  (hG : IsReductive G) (d : D ⟶ G) [Mono d.hom.hom]
  (hd : IsClosedSubgroup d) (hD : IsReductive D)
  (hss : ∀ s : S, IsSemisimple (geometricFiber D s))
  (q : G ⟶ Q) (hQ : RelativeTorus.IsTorus Q)
  (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range d) q)
  (t : T.toGrp ⟶ G) (ht : IsClosedSubgroup t) (hmax : IsFibrewiseMaximalTorus t)

include hG hd hD hss hQ hq hmax in
/-- At every field-valued point, the full intersection with the supplied
relative derived subgroup is a maximal torus of that subgroup. -/
theorem isMaximalTorus_relativeDerivedIntersection_fieldFiber
    {k : Type u} [Field k] (b : Spec (CommRingCat.of k) ⟶ S) :
    IsMaximalTorus
      (commutativeSubgroupIntersectionSnd
        (T := (CommGroupScheme.baseChange b).obj T)
        ((baseChange b).map t) ((baseChange b).map d)) := by
  let : Smooth G.X.hom := hG.smooth
  let : IsAffineHom G.X.hom := hG.isAffineHom
  exact isMaximalTorus_commutativeSubgroupIntersectionSnd_derived
    (T := (CommGroupScheme.baseChange b).obj T)
    (hG.isConnectedReductive_baseChange b) ((baseChange b).map d)
    (isDerivedSubgroup_fieldFiber_of_semisimple_torusQuotient d hd hD hss q hQ hq b)
    ((baseChange b).map t) (hmax.fieldPoint b)

include hG hd hD hss hQ hq hmax in
/-- The actual commutative intersection is maximal on every residue fibre. -/
theorem isFibrewiseMaximalTorus_relativeDerivedIntersection :
    IsFibrewiseMaximalTorus (commutativeSubgroupIntersectionSnd t d) := by
  intro s
  let b := S.fromSpecResidueField s
  let e := subgroupIntersectionBaseChangeIso b t d
  have hm := isMaximalTorus_relativeDerivedIntersection_fieldFiber
    hG d hd hD hss q hQ hq t hmax b
  have he : e.hom ≫ commutativeSubgroupIntersectionSnd
      (T := (CommGroupScheme.baseChange b).obj T)
      ((baseChange b).map t) ((baseChange b).map d) =
      (baseChange b).map (commutativeSubgroupIntersectionSnd t d) :=
    PreservesPullback.iso_hom_snd (baseChange b) t d
  change IsMaximalTorus
    (T := (CommGroupScheme.baseChange b).obj (commutativeSubgroupIntersection t d))
    ((baseChange b).map (commutativeSubgroupIntersectionSnd t d))
  rw [← he]
  exact hm.iso_comp
    (T := commutativeSubgroupIntersection
      (T := (CommGroupScheme.baseChange b).obj T)
      ((baseChange b).map t) ((baseChange b).map d))
    (T' := (CommGroupScheme.baseChange b).obj (commutativeSubgroupIntersection t d)) e

include hG hd hD hss hQ hq ht hmax in
/-- The whole intersection of a relative maximal torus with the supplied
relative derived subgroup is a relative torus over the original base. -/
theorem relativeTorus_relativeDerivedIntersection
    (hT : RelativeTorus.IsTorus T.toGrp)
    (hn : (SubgroupFunctor.range d).IsNormal) :
    RelativeTorus.IsTorus (commutativeSubgroupIntersection t d).toGrp := by
  let A := commutativeSubgroupIntersection t d
  have hs : Smooth A.X.hom := by
    exact smooth_of_over_iso
      ((Grp.forget _).mapIso (pullbackSymmetry t d))
      (normal_subgroupIntersection_relativeMaximalTorus_smooth
        hG hT t ht hmax d hd hn hD.smooth hD.isAffineHom)
  have ha : IsAffineHom A.X.hom := by
    let : IsAffineHom T.X.hom := hT.isAffineHom
    let : IsClosedImmersion (commutativeSubgroupIntersectionFst t d).hom.hom.left :=
      isClosedSubgroup_commutativeSubgroupIntersectionFst t d hd
    rw [← Over.w (commutativeSubgroupIntersectionFst t d).hom.hom]
    infer_instance
  apply relativeTorus_of_commutative_reductive A
  refine ⟨hs, ha, fun s => ?_⟩
  let b := geometricPoint S s
  have hm := isMaximalTorus_relativeDerivedIntersection_fieldFiber
    hG d hd hD hss q hQ hq t hmax b
  have htorus : IsTorus (geometricFiber A.toGrp s) :=
    IsTorus.of_iso (subgroupIntersectionBaseChangeIso b t d) hm.1
  exact htorus.isConnectedReductive_of_fieldSplitting.isPseudoReductive

/-- The canonical maximal-torus presentation of the full intersection with
the relative derived subgroup, retaining its range in the specified subgroup. -/
def relativeDerivedMaximalTorusIntersection
    (hT : RelativeTorus.IsTorus T.toGrp)
    (hn : (SubgroupFunctor.range d).IsNormal) :
    Σ A : CommGroupScheme S, { i : A.toGrp ⟶ D //
      RelativeTorus.IsTorus A.toGrp ∧ IsClosedSubgroup i ∧
      IsFibrewiseMaximalTorus i ∧
      SubgroupFunctor.range i = SubgroupFunctor.range (subgroupIntersectionFst d t) } := by
  refine ⟨commutativeSubgroupIntersection t d, commutativeSubgroupIntersectionSnd t d,
    relativeTorus_relativeDerivedIntersection hG d hd hD hss q hQ hq t ht hmax hT hn,
    isClosedSubgroup_commutativeSubgroupIntersectionSnd t d ht,
    isFibrewiseMaximalTorus_relativeDerivedIntersection hG d hd hD hss q hQ hq t hmax, ?_⟩
  have he : (pullbackSymmetry t d).hom ≫ subgroupIntersectionFst d t =
      commutativeSubgroupIntersectionSnd t d := pullbackSymmetry_hom_comp_fst t d
  rw [← he, SubgroupFunctor.range_iso_comp]

end Intersection

end Langlands.GroupScheme
