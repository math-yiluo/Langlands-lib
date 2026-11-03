import Langlands.GroupScheme.Dynamic.Representability

/-! # Closed intersections in corepresented affine groups -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace SubgroupFunctor

variable {S : Scheme.{u}} {G : GroupScheme S} {Index : Sort v}

/-- The pointwise intersection of a family of subgroup functors. -/
def intersection (K : Index → SubgroupFunctor G) : SubgroupFunctor G where
  carrier T := ⨅ a, (K a).carrier T
  comp_mem a x hx := by
    simp only [Subgroup.mem_iInf] at hx ⊢
    exact fun b => (K b).comp_mem a (hx b)

@[simp] theorem mem_intersection {K : Index → SubgroupFunctor G} {T : Over S}
    {x : T ⟶ G.X} :
    x ∈ (intersection K).carrier T ↔ ∀ a, x ∈ (K a).carrier T :=
  Subgroup.mem_iInf

end SubgroupFunctor

namespace Corepresented

variable {R : CommRingCat.{u}} {F : CommAlgCat.{u} R ⥤ GrpCat.{u}}
  {B : CommAlgCat.{u} R} {e : (F ⋙ forget GrpCat).CorepresentableBy B}
  {Index : Sort v} {K : Index → SubgroupFunctor (groupScheme F e)} {I : Index → Ideal B}

/-- The intersection of functors cut out by ideals is cut out by their sum. -/
theorem isAffineCutOutBy_intersection (hK : ∀ a, IsAffineCutOutBy e (K a) (I a)) :
    IsAffineCutOutBy e (SubgroupFunctor.intersection K) (⨆ a, I a) := by
  intro A f x
  rw [SubgroupFunctor.mem_intersection]
  constructor
  · intro hx
    have hker : (⨆ a, I a) ≤ RingHom.ker (pointRing x).hom :=
      iSup_le fun a b hb => RingHom.mem_ker.mpr (((hK a) A f x).mp (hx a) b hb)
    exact fun b hb => RingHom.mem_ker.mp (hker hb)
  · intro hx a
    exact ((hK a) A f x).mpr fun b hb => hx b ((le_iSup I a) hb)

/-- The closed affine group scheme representing an intersection of ideal-cut subgroup functors. -/
abbrev intersectionScheme (hK : ∀ a, IsAffineCutOutBy e (K a) (I a)) :
    GroupScheme (Spec R) :=
  cutGroupScheme (isCutOutBy_affineSubgroups (isAffineCutOutBy_intersection hK))

/-- The closed inclusion of the ideal-cut intersection into its ambient group. -/
abbrev intersectionHom (hK : ∀ a, IsAffineCutOutBy e (K a) (I a)) :
    intersectionScheme hK ⟶ groupScheme F e :=
  cutHom _

/-- The ideal-sum construction represents the intersection on every test scheme. -/
theorem isRepresentedBy_intersectionHom (hK : ∀ a, IsAffineCutOutBy e (K a) (I a)) :
    (SubgroupFunctor.intersection K).IsRepresentedBy (intersectionHom hK) :=
  isRepresentedBy_cutHom_affineSubgroups (isAffineCutOutBy_intersection hK)

theorem isClosedSubgroup_intersectionHom (hK : ∀ a, IsAffineCutOutBy e (K a) (I a)) :
    IsClosedSubgroup (intersectionHom hK) :=
  isClosedSubgroup_cutHom _

end Corepresented

end Langlands.GroupScheme
