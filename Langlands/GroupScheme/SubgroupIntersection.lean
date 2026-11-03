import Langlands.GroupScheme.Reductive.Basic

/-! # Scheme-theoretic intersections of closed subgroups -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {S : Scheme.{u}} {P P' G : GroupScheme S}

/-- The scheme-theoretic intersection of two subgroup presentations. -/
def subgroupIntersection (j : P ⟶ G) (j' : P' ⟶ G) : GroupScheme S :=
  pullback j j'

/-- The first projection of a subgroup intersection. -/
def subgroupIntersectionFst (j : P ⟶ G) (j' : P' ⟶ G) :
    subgroupIntersection j j' ⟶ P :=
  pullback.fst j j'

/-- The second projection of a subgroup intersection. -/
def subgroupIntersectionSnd (j : P ⟶ G) (j' : P' ⟶ G) :
    subgroupIntersection j j' ⟶ P' :=
  pullback.snd j j'

/-- The inclusion of the intersection into the ambient group. -/
def subgroupIntersectionHom (j : P ⟶ G) (j' : P' ⟶ G) :
    subgroupIntersection j j' ⟶ G :=
  subgroupIntersectionFst j j' ≫ j

theorem subgroupIntersection_condition (j : P ⟶ G) (j' : P' ⟶ G) :
    subgroupIntersectionFst j j' ≫ j = subgroupIntersectionSnd j j' ≫ j' :=
  pullback.condition

/-- The underlying schemes over the base form the intersection pullback. -/
theorem subgroupIntersection_isPullback (j : P ⟶ G) (j' : P' ⟶ G) :
    IsPullback (subgroupIntersectionFst j j').hom.hom
      (subgroupIntersectionSnd j j').hom.hom j.hom.hom j'.hom.hom :=
  (IsPullback.of_hasPullback j j').map (Grp.forget (Over S))

/-- The same pullback after forgetting the structure maps to the base. -/
theorem subgroupIntersection_isPullback_scheme (j : P ⟶ G) (j' : P' ⟶ G) :
    IsPullback (subgroupIntersectionFst j j').hom.hom.left
      (subgroupIntersectionSnd j j').hom.hom.left j.hom.hom.left j'.hom.hom.left :=
  (subgroupIntersection_isPullback j j').map (Over.forget S)

/-- The projection of a scheme-theoretic intersection to the first group is
closed whenever the second embedding is closed. -/
theorem isClosedSubgroup_subgroupIntersectionFst (j : P ⟶ G) {i : P' ⟶ G}
    (hi : IsClosedSubgroup i) : IsClosedSubgroup (subgroupIntersectionFst j i) := by
  change IsClosedImmersion (subgroupIntersectionFst j i).hom.hom.left
  exact MorphismProperty.of_isPullback (subgroupIntersection_isPullback_scheme j i).flip hi

/-- A point lies in the actual intersection exactly when it lies in both
subgroup ranges, on every test scheme. -/
theorem range_subgroupIntersectionHom (j : P ⟶ G) (j' : P' ⟶ G) :
    SubgroupFunctor.range (subgroupIntersectionHom j j') =
      SubgroupFunctor.range j ⊓ SubgroupFunctor.range j' := by
  apply SubgroupFunctor.ext
  intro T
  apply Subgroup.ext
  intro x
  change (∃ y : T ⟶ (subgroupIntersection j j').X,
      y ≫ (subgroupIntersectionHom j j').hom.hom = x) ↔
    (∃ y : T ⟶ P.X, y ≫ j.hom.hom = x) ∧
      (∃ y : T ⟶ P'.X, y ≫ j'.hom.hom = x)
  let hpb := subgroupIntersection_isPullback j j'
  constructor
  · rintro ⟨y, rfl⟩
    constructor
    · exact ⟨y ≫ (subgroupIntersectionFst j j').hom.hom,
        Category.assoc _ _ _⟩
    · refine ⟨y ≫ (subgroupIntersectionSnd j j').hom.hom, ?_⟩
      change (y ≫ (subgroupIntersectionSnd j j').hom.hom) ≫ j'.hom.hom =
        y ≫ (subgroupIntersectionFst j j').hom.hom ≫ j.hom.hom
      rw [Category.assoc, ← hpb.w]
  · rintro ⟨⟨y, hy⟩, ⟨z, hz⟩⟩
    refine ⟨hpb.lift y z (hy.trans hz.symm), ?_⟩
    change (hpb.lift y z _ ≫ (subgroupIntersectionFst j j').hom.hom) ≫ j.hom.hom = x
    rw [hpb.lift_fst]
    exact hy

/-- The intersection of two closed subgroup schemes is a closed subgroup. -/
theorem isClosedSubgroup_subgroupIntersectionHom {j : P ⟶ G} {j' : P' ⟶ G}
    (hj : IsClosedSubgroup j) (hj' : IsClosedSubgroup j') :
    IsClosedSubgroup (subgroupIntersectionHom j j') := by
  have : IsClosedImmersion j.hom.hom.left := hj
  have : IsClosedImmersion (subgroupIntersectionFst j j').hom.hom.left :=
    MorphismProperty.of_isPullback
      (subgroupIntersection_isPullback_scheme j j').flip hj'
  change IsClosedImmersion
    ((subgroupIntersectionFst j j').hom.hom.left ≫ j.hom.hom.left)
  infer_instance

/-- The closed intersection represents the pointwise intersection functor. -/
theorem isRepresentedBy_subgroupIntersectionHom {j : P ⟶ G} {j' : P' ⟶ G}
    (hj : IsClosedSubgroup j) (hj' : IsClosedSubgroup j') :
    (SubgroupFunctor.range j ⊓ SubgroupFunctor.range j').IsRepresentedBy
      (subgroupIntersectionHom j j') := by
  have : IsClosedImmersion (subgroupIntersectionHom j j').hom.hom.left :=
    isClosedSubgroup_subgroupIntersectionHom hj hj'
  exact ⟨Over.mono_of_mono_left _, range_subgroupIntersectionHom j j'⟩

/-- Scheme-theoretic subgroup intersections commute with arbitrary base change. -/
def subgroupIntersectionBaseChangeIso {S' : Scheme.{u}} (b : S' ⟶ S)
    (j : P ⟶ G) (j' : P' ⟶ G) :
    (GroupScheme.baseChange b).obj (subgroupIntersection j j') ≅
      subgroupIntersection ((GroupScheme.baseChange b).map j)
        ((GroupScheme.baseChange b).map j') :=
  PreservesPullback.iso (GroupScheme.baseChange b) j j'

@[reassoc (attr := simp)]
theorem subgroupIntersectionBaseChangeIso_hom_ι {S' : Scheme.{u}} (b : S' ⟶ S)
    (j : P ⟶ G) (j' : P' ⟶ G) :
    (subgroupIntersectionBaseChangeIso b j j').hom ≫
      subgroupIntersectionHom ((GroupScheme.baseChange b).map j)
        ((GroupScheme.baseChange b).map j') =
      (GroupScheme.baseChange b).map (subgroupIntersectionHom j j') := by
  change (PreservesPullback.iso (GroupScheme.baseChange b) j j').hom ≫
      (pullback.fst _ _ ≫ (GroupScheme.baseChange b).map j) =
    (GroupScheme.baseChange b).map (pullback.fst j j' ≫ j)
  rw [PreservesPullback.iso_hom_fst_assoc, ← Functor.map_comp]

end Langlands.GroupScheme
