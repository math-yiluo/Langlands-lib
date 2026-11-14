import Langlands.GroupScheme.RelativeLevi.ParabolicLocality
import Langlands.GroupScheme.SubgroupFunctor.MonicGluing

/-! # Effective Zariski descent of actual relative parabolic subgroups -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.ParabolicSubgroupModuli

variable {S : Scheme.{u}} {G : GroupScheme S}

/-- Every actual parabolic subgroup has Zariski-local membership on all tests. -/
theorem isZariskiLocal_of_isParabolic (F : ParabolicSubgroup G) :
    SubgroupFunctor.IsZariskiLocal F.val :=
  (parabolicRepresentative F).represents.isZariskiLocal

/-- A Zariski-local subgroup functor is parabolic if its restrictions to a
base open cover are represented by actual relative parabolics. -/
theorem isParabolic_of_openCover (hG : IsReductive G)
    {F : SubgroupFunctor G} (hF : SubgroupFunctor.IsZariskiLocal F)
    (𝒰 : Scheme.OpenCover.{u} S)
    (h : ∀ i, IsParabolic (F.baseChange (𝒰.f i))) : IsParabolic F := by
  obtain ⟨P, j, hj⟩ := F.exists_isRepresentedBy_of_openCover hF 𝒰 (fun i => by
    let r := parabolicRepresentative ⟨F.baseChange (𝒰.f i), h i⟩
    exact ⟨r.group, r.hom, r.represents⟩)
  exact isParabolic_of_isRepresentedBy_of_openCover hG hj 𝒰 h

variable (𝒰 : Scheme.OpenCover.{u} S)
    (F : ∀ i, ParabolicSubgroup ((GroupScheme.baseChange (𝒰.f i)).obj G))

/-- Matching actual local parabolic subgroups descend to an actual global
parabolic subgroup, with no global representative supplied as a hypothesis. -/
theorem isParabolic_descentSubgroup (hG : IsReductive G)
    (hF : SubgroupFunctor.IsMatching 𝒰 (fun i => (F i).val)) :
    IsParabolic (SubgroupFunctor.descentSubgroup 𝒰 (fun i => (F i).val)) := by
  apply isParabolic_of_openCover hG
    (SubgroupFunctor.isZariskiLocal_descentSubgroup 𝒰 _
      (fun i => isZariskiLocal_of_isParabolic (F i))) 𝒰
  intro i
  rw [SubgroupFunctor.baseChange_descentSubgroup 𝒰 _ hF i]
  exact (F i).property

/-- The actual parabolic subgroup constructed from matching local subgroups. -/
def descentParabolic (hG : IsReductive G)
    (hF : SubgroupFunctor.IsMatching 𝒰 (fun i => (F i).val)) : ParabolicSubgroup G :=
  ⟨SubgroupFunctor.descentSubgroup 𝒰 (fun i => (F i).val),
    isParabolic_descentSubgroup 𝒰 F hG hF⟩

/-- The descended parabolic has precisely the prescribed local base changes. -/
theorem baseChange_descentParabolic (hG : IsReductive G)
    (hF : SubgroupFunctor.IsMatching 𝒰 (fun i => (F i).val)) (i : 𝒰.I₀) :
    (descentParabolic 𝒰 F hG hF).val.baseChange (𝒰.f i) = (F i).val :=
  SubgroupFunctor.baseChange_descentSubgroup 𝒰 _ hF i

/-- The descended parabolic is the unique actual parabolic with these local
base changes. -/
theorem eq_descentParabolic (hG : IsReductive G)
    (hF : SubgroupFunctor.IsMatching 𝒰 (fun i => (F i).val))
    (H : ParabolicSubgroup G)
    (hH : ∀ i, H.val.baseChange (𝒰.f i) = (F i).val) :
    H = descentParabolic 𝒰 F hG hF := by
  apply eq_of_baseChange_openCover 𝒰
  intro i
  rw [baseChange_descentParabolic, hH i]

end Langlands.GroupScheme.ParabolicSubgroupModuli
