import Langlands.GroupScheme.HomScheme.AdmissibleDescent
import Langlands.GroupScheme.RepresentabilityTransfer
import Langlands.GroupScheme.Torus.Locality

/-! # Absolute membership and torus locality for actual subgroups -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.SubgroupFunctor

variable {S : Scheme.{u}} {G : GroupScheme S} (F : SubgroupFunctor G)

/-- Membership in an actual subgroup, expressed on absolute scheme maps to
its ambient scheme with the induced base map. -/
def schemeCondition {Y : Scheme.{u}} (x : Y ⟶ G.X.left) : Prop :=
  (Over.homMk x rfl : Over.mk (x ≫ G.X.hom) ⟶ G.X) ∈
    F.carrier (Over.mk (x ≫ G.X.hom))

/-- The absolute condition retains exactly the original all-test membership. -/
theorem schemeCondition_iff_mem {T : Over S} (x : T ⟶ G.X) :
    F.schemeCondition x.left ↔ x ∈ F.carrier T := by
  let p : Over.mk (x.left ≫ G.X.hom) ⟶ G.X := Over.homMk x.left rfl
  let a : T ⟶ Over.mk (x.left ≫ G.X.hom) :=
    Over.homMk (𝟙 _) (by
      change (𝟙 T.left) ≫ (x.left ≫ G.X.hom) = T.hom
      simpa only [Category.id_comp] using Over.w x)
  let b : Over.mk (x.left ≫ G.X.hom) ⟶ T :=
    Over.homMk (𝟙 _) (by
      change (𝟙 T.left) ≫ T.hom = x.left ≫ G.X.hom
      simpa only [Category.id_comp] using (Over.w x).symm)
  have ha : a ≫ p = x := Over.OverMorphism.ext (Category.id_comp _)
  have hb : b ≫ x = p := Over.OverMorphism.ext (Category.id_comp _)
  constructor
  · intro hx
    have h := F.comp_mem a hx
    rwa [ha] at h
  · intro hx
    have h := F.comp_mem b hx
    rwa [hb] at h

/-- The absolute condition is stable under arbitrary scheme restriction. -/
theorem schemeCondition_comp {Y Z : Scheme.{u}} (x : Y ⟶ G.X.left)
    (a : Z ⟶ Y) (hx : F.schemeCondition x) : F.schemeCondition (a ≫ x) := by
  let p : Over.mk (x ≫ G.X.hom) ⟶ G.X := Over.homMk x rfl
  let b : Over.mk ((a ≫ x) ≫ G.X.hom) ⟶ Over.mk (x ≫ G.X.hom) :=
    Over.homMk a (Category.assoc _ _ _).symm
  exact (F.schemeCondition_iff_mem (b ≫ p)).mpr (F.comp_mem b hx)

/-- Local membership in the subgroup gives locality on absolute scheme maps. -/
theorem schemeCondition_iff_openCover (hF : IsZariskiLocal F)
    {Y : Scheme.{u}} (x : Y ⟶ G.X.left) (𝒱 : Scheme.OpenCover.{u} Y) :
    F.schemeCondition x ↔ ∀ i, F.schemeCondition (𝒱.f i ≫ x) := by
  let T : Over S := Over.mk (x ≫ G.X.hom)
  let p : T ⟶ G.X := Over.homMk x rfl
  change p ∈ F.carrier T ↔ _
  rw [hF T 𝒱 p]
  apply forall_congr'
  intro i
  exact (F.schemeCondition_iff_mem (coverMap 𝒱 i ≫ p)).symm

/-- The absolute condition agrees with actual membership after any ambient
base change, using the original pullback projection. -/
theorem schemeCondition_baseChange_iff {B : Scheme.{u}} (b : B ⟶ S)
    {Y : Scheme.{u}} (x : Y ⟶ ((GroupScheme.baseChange b).obj G).X.left) :
    F.schemeCondition (x ≫ pullback.fst G.X.hom b) ↔
      schemeCondition (G := (GroupScheme.baseChange b).obj G) (F.baseChange b) x := by
  let T : Over B := Over.mk (x ≫ pullback.snd G.X.hom b)
  let p : T ⟶ ((GroupScheme.baseChange b).obj G).X := Over.homMk x rfl
  let q : (Over.map b).obj T ⟶ G.X := baseChangePointsEquiv b G T p
  have hq : q.left = x ≫ pullback.fst G.X.hom b :=
    baseChangePointsEquiv_left b G T p
  calc F.schemeCondition (x ≫ pullback.fst G.X.hom b) ↔
        F.schemeCondition q.left := by rw [hq]
    _ ↔ q ∈ F.carrier ((Over.map b).obj T) := F.schemeCondition_iff_mem q
    _ ↔ p ∈ (F.baseChange b).carrier T := Iff.rfl
    _ ↔ schemeCondition (G := (GroupScheme.baseChange b).obj G) (F.baseChange b) x :=
          (schemeCondition_iff_mem (G := (GroupScheme.baseChange b).obj G)
            (F.baseChange b) p).symm

/-- A represented subgroup's absolute condition is factorization through
the same actual underlying scheme map. -/
theorem schemeCondition_iff_exists_of_isRepresentedBy
    {K : GroupScheme S} {j : K ⟶ G} (hj : F.IsRepresentedBy j)
    {Y : Scheme.{u}} (x : Y ⟶ G.X.left) :
    F.schemeCondition x ↔
      ∃ a : Y ⟶ K.X.left, a ≫ j.hom.hom.left = x := by
  let T : Over S := Over.mk (x ≫ G.X.hom)
  let p : T ⟶ G.X := Over.homMk x rfl
  change p ∈ F.carrier T ↔ _
  rw [← hj.2, mem_range]
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a.left, congrArg (fun f => f.left) ha⟩
  · rintro ⟨a, ha⟩
    let a' : T ⟶ K.X := Over.homMk a (by
      change a ≫ K.X.hom = x ≫ G.X.hom
      rw [← Over.w j.hom.hom, ← Category.assoc, ha])
    exact ⟨a', Over.OverMorphism.ext ha⟩

end Langlands.GroupScheme.SubgroupFunctor

namespace Langlands.GroupScheme.TorusSubgroupModuli

variable {S : Scheme.{u}} {G : GroupScheme S}

/-- A closed representative is a torus whenever its subgroup is locally
admissible on a Zariski cover of the base. -/
theorem isAdmissible_of_isClosedRepresentable_of_openCover
    {F : SubgroupFunctor G} (hF : F.IsClosedRepresentable)
    (𝒰 : Scheme.OpenCover.{u} S)
    (h : ∀ i, IsAdmissible (F.baseChange (𝒰.f i))) : IsAdmissible F := by
  obtain ⟨K, j, hj, hc⟩ := hF
  refine ⟨K, j, hc, ?_, hj⟩
  apply RelativeTorus.IsTorus.of_openCover 𝒰
  intro i
  let r := admissibleRepresentative ⟨F.baseChange (𝒰.f i), h i⟩
  exact RelativeTorus.IsTorus.of_iso
    ((hj.baseChange (𝒰.f i)).isoOfIsRepresentedBy r.represents) r.torus

end Langlands.GroupScheme.TorusSubgroupModuli
