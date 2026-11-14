import Langlands.GroupScheme.Rational.TorusCentralizerRegularCocharacter
import Langlands.GroupScheme.Absolute.RegularCocharacterBorelProof
import Langlands.GroupScheme.Absolute.GeometricBorelDescent
import Langlands.GroupScheme.Dynamic.BaseRepresentabilityProof
import Langlands.GroupScheme.Dynamic.BaseSmoothConnectedProof
import Langlands.GroupScheme.Dynamic.OppositeIntersection
import Langlands.GroupScheme.Reductive.BaseChange
import Langlands.GroupScheme.Reductive.SteinbergBigCellGeometry
import Langlands.GroupScheme.Torus.FieldPointMaximality
import Langlands.GroupScheme.RelativeLevi.Borel
import Langlands.GroupScheme.Descent.Data

/-! # Relative Borels from cocharacters with a maximal-torus centralizer -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

variable {S : Scheme.{u}} {G B : GroupScheme S} {T : CommGroupScheme S}

/-- A cocharacter with the given split maximal torus as its entire
centralizer has a relative Borel as each monomorphic parabolic representative. -/
theorem isRelativeBorelSubgroup_of_torusCentralizer
    (hG : IsReductive G) (hT : IsSplitTorus T.toGrp)
    (t : T.toGrp ⟶ G) (ht : IsClosedSubgroup t)
    (hmax : IsFibrewiseMaximalTorus t) (ν : cocharacterLattice T)
    (hZ : Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ t) =
      SubgroupFunctor.range t)
    (j : B ⟶ G)
    (hj : (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ t)).IsRepresentedBy j) :
    IsRelativeBorelSubgroup j := by
  have : IsAffineHom G.X.hom := hG.isAffineHom
  have : Smooth G.X.hom := hG.smooth
  have : IsClosedImmersion t.hom.hom.left := ht
  have : Mono t.hom.hom := Over.mono_of_mono_left _
  have hzrep : (Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ t)).IsRepresentedBy t :=
    ⟨inferInstance, hZ.symm⟩
  have hjclosed : IsClosedSubgroup j := by
    obtain ⟨P, p, hpclosed, _, hprep⟩ :=
      (dynamicBaseRepresentability S G (CommGroupScheme.groupHom ν ≫ t)).1
    rw [← hj.isoOfIsRepresentedBy_hom_comp hprep]
    exact (IsClosedSubgroup.of_iso (hj.isoOfIsRepresentedBy hprep)).comp hpclosed
  have hfield : ∀ (k : Type u) [Field k] (b : Spec (CommRingCat.of k) ⟶ S),
      IsBorelSubgroup ((GroupScheme.baseChange b).map j) := by
    intro k _ b
    let G' := (GroupScheme.baseChange b).obj G
    let T' := (CommGroupScheme.baseChange b).obj T
    let t' := (GroupScheme.baseChange b).map t
    let ν' := cocharacterLattice.baseChange b T ν
    have hG' : IsConnectedReductive G' := hG.isConnectedReductive_baseChange b
    have : IsAffineHom G'.X.hom := hG'.isAffineHom
    have : Smooth G'.X.hom := hG'.smooth
    have hT' : IsSplitTorus T'.toGrp := hT.baseChange b
    have hmax' : IsMaximalTorus (T := T') t' := hmax.fieldPoint b
    have hνbase : Dynamic.baseChangeCocharacter b (CommGroupScheme.groupHom ν ≫ t) =
        CommGroupScheme.groupHom ν' ≫ t' := by
      rw [Dynamic.baseChangeCocharacter_comp, ← cocharacterLattice.groupHom_baseChange_dynamic]
    have hZ' := hzrep.baseChange b
    rw [← Dynamic.centralizer_baseChange, hνbase] at hZ'
    have hν' : IsRegularCocharacter t' ν' :=
      isRegularCocharacter_of_centralizer_isRepresentedBy_torus hT' t' ν' hZ'
    have hj' := hj.baseChange b
    rw [← Dynamic.parabolic_baseChange, hνbase] at hj'
    exact (regularCocharacterBorel k G' hG' T' t' hT' hmax').1 ν' hν' _ _
      (hjclosed.baseChange b) hj'
  have hgeo : ∀ s : S, IsGeometricBorelSubgroup (RelativeLevi.residueFiberHom j s) := by
    intro s
    let f := S.fromSpecResidueField s
    let q := toAlgebraicClosure (S.residueField s)
    let r := q ≫ f
    let eB := Descent.pullbackComparison f q r rfl B
    let eG := Descent.pullbackComparison f q r rfl G
    have : IsAffineHom ((GroupScheme.baseChange f).obj G).X.hom :=
      MorphismProperty.pullback_snd (P := @IsAffineHom) G.X.hom f hG.isAffineHom
    have h := ((hfield _ r).iso_comp eB).comp_iso eG.symm
    change IsBorelSubgroup
      ((eB.hom ≫ (GroupScheme.baseChange r).map j) ≫ eG.inv) at h
    rw [← Descent.pullbackComparison_naturality, Category.assoc,
      Iso.hom_inv_id, Category.comp_id] at h
    exact isGeometricBorelSubgroup_of_baseChange_toAlgebraicClosure h
      (hjclosed.baseChange f)
  have : IsClosedImmersion j.hom.hom.left := hjclosed
  exact
    { isRelativeParabolicSubgroup :=
        { smooth := (dynamicBaseSmoothConnected S G
            (CommGroupScheme.groupHom ν ≫ t) B j).2.1 hj |>.1
          isAffineHom := hjclosed.isAffineHom
          mono := hj.1
          residueFiber := fun s => (hgeo s).isParabolicSubgroup }
      residueFiber := hgeo }

/-- Reversing a cocharacter with a split maximal-torus centralizer
also gives a relative Borel in every monomorphic parabolic presentation. -/
theorem isRelativeBorelSubgroup_opposite_of_torusCentralizer
    (hG : IsReductive G) (hT : IsSplitTorus T.toGrp)
    (t : T.toGrp ⟶ G) (ht : IsClosedSubgroup t)
    (hmax : IsFibrewiseMaximalTorus t) (ν : cocharacterLattice T)
    (hZ : Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ t) =
      SubgroupFunctor.range t)
    (j : B ⟶ G)
    (hj : (Dynamic.parabolic
      (Dynamic.oppositeCocharacter (CommGroupScheme.groupHom ν ≫ t))).IsRepresentedBy j) :
    IsRelativeBorelSubgroup j := by
  have hneg : CommGroupScheme.groupHom (-ν) ≫ t =
      Dynamic.oppositeCocharacter (CommGroupScheme.groupHom ν ≫ t) := by
    have hν : Gm.powerHom S (-1) ≫ ν = -ν := by
      simp only [Gm.powerHom_apply, neg_one_zsmul, Preadditive.neg_comp, Category.id_comp]
    rw [Dynamic.oppositeCocharacter, ← Category.assoc]
    change CommGroupScheme.groupHom (-ν) ≫ t =
      CommGroupScheme.groupHom (Gm.powerHom _ (-1) ≫ ν) ≫ t
    rw [hν]
  apply isRelativeBorelSubgroup_of_torusCentralizer hG hT t ht hmax (-ν)
  · rw [hneg, Dynamic.centralizer_oppositeCocharacter]
    exact hZ
  · rwa [hneg]

namespace RelativeLevi

/-- An actual closed relative Borel representing the full dynamic parabolic
of the displayed cocharacter. -/
structure DynamicBorelData (χ : (Gm S).toGrp ⟶ G) where
  obj : GroupScheme S
  inclusion : obj ⟶ G
  borel : IsRelativeBorelSubgroup inclusion
  closed : IsClosedSubgroup inclusion
  range_eq : SubgroupFunctor.range inclusion = Dynamic.parabolic χ

end RelativeLevi

/-- Choose an actual negative relative Borel from a cocharacter whose
centralizer is the supplied split maximal torus. -/
def oppositeBorelOfTorusCentralizer
    (hG : IsReductive G) (hT : IsSplitTorus T.toGrp)
    (t : T.toGrp ⟶ G) (ht : IsClosedSubgroup t)
    (hmax : IsFibrewiseMaximalTorus t) (ν : cocharacterLattice T)
    (hZ : Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ t) =
      SubgroupFunctor.range t) :
    RelativeLevi.DynamicBorelData
      (Dynamic.oppositeCocharacter (CommGroupScheme.groupHom ν ≫ t)) :=
  Classical.choice <| by
    have : IsAffineHom G.X.hom := hG.isAffineHom
    have : Smooth G.X.hom := hG.smooth
    obtain ⟨C, j, hjclosed, _, hjrep⟩ :=
      (dynamicBaseRepresentability S G
        (Dynamic.oppositeCocharacter (CommGroupScheme.groupHom ν ≫ t))).1
    exact ⟨⟨C, j,
      isRelativeBorelSubgroup_opposite_of_torusCentralizer hG hT t ht hmax ν hZ j hjrep,
      hjclosed, hjrep.2⟩⟩

/-- The selected negative Borel supplies the actual existence clause used
in an étale-local dynamic presentation. -/
theorem exists_oppositeBorel_of_torusCentralizer
    (hG : IsReductive G) (hT : IsSplitTorus T.toGrp)
    (t : T.toGrp ⟶ G) (ht : IsClosedSubgroup t)
    (hmax : IsFibrewiseMaximalTorus t) (ν : cocharacterLattice T)
    (hZ : Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ t) =
      SubgroupFunctor.range t) :
    ∃ (C : GroupScheme S) (j : C ⟶ G),
      IsRelativeBorelSubgroup j ∧ IsClosedSubgroup j ∧
        SubgroupFunctor.range j =
          Dynamic.parabolic
            (Dynamic.oppositeCocharacter (CommGroupScheme.groupHom ν ≫ t)) := by
  let D := oppositeBorelOfTorusCentralizer hG hT t ht hmax ν hZ
  exact ⟨D.obj, D.inclusion, D.borel, D.closed, D.range_eq⟩

end Langlands.GroupScheme
