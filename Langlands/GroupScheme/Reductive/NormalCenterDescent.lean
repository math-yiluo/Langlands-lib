import Langlands.GroupScheme.Reductive.NormalCenterReduction
import Langlands.GroupScheme.Derived.CentralIntersectionReduction
import Langlands.GroupScheme.SubgroupFunctor.FpqcDescent
import Langlands.GroupScheme.BaseChangeReflection
import Langlands.GroupScheme.Absolute.AlgebraicClosureBaseChange

/-! # Descent of full-centre containment for normal reductive subgroups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Full-centre containment descends along an fpqc base change when the ambient
full centre has a closed representative. -/
theorem center_le_comap_of_baseChange_le
    {S S' : Scheme.{u}} (b : S' ⟶ S)
    [QuasiCompact b] [Flat b] [Surjective b]
    {G H Z : GroupScheme S} (i : H ⟶ G) (z : Z ⟶ G)
    (hz : IsSchemeTheoreticCenter z)
    (h : center ((GroupScheme.baseChange b).obj H) ≤
      (center ((GroupScheme.baseChange b).obj G)).comap
        ((GroupScheme.baseChange b).map i)) :
    center H ≤ (center G).comap i := by
  let j := subgroupIntersectionFst i z
  have hj : IsClosedSubgroup j := isClosedSubgroup_subgroupIntersectionFst i hz.1
  let : IsClosedImmersion j.hom.hom.left := hj
  let : Mono j.hom.hom := Over.mono_of_mono_left _
  have hr : SubgroupFunctor.range j = (center G).comap i :=
    range_subgroupIntersectionFst_of_isSchemeTheoreticCenter i hz
  rw [← hr]
  apply SubgroupFunctor.le_range_of_baseChange_le b j
  rw [hr, SubgroupFunctor.comap_baseChange, ← center_baseChange, ← center_baseChange]
  exact h

/-- The fixed centre-containing split-torus proposition implies full-centre
containment for normal connected reductive subgroups over every field. -/
theorem normalReductiveCenter_of_fixedCenterContainingTorus
    (hFixed : FixedCenterContainingTorusStatement.{u}) :
    NormalReductiveCenterStatement.{u} := by
  intro k _ G H hG hH i hi hn
  let b := toAlgebraicClosure k
  obtain ⟨Z, z, hz⟩ := schemeTheoreticCenterExistence k G hG
  obtain ⟨hsurj, hflat, hqc⟩ := fieldExtension_fpqc k (AlgebraicClosure k)
  let : Surjective b := hsurj
  let : Flat b := hflat
  let : QuasiCompact b := hqc
  apply center_le_comap_of_baseChange_le b i z hz
  apply center_le_comap_of_normal_of_fixedCenterContainingTorus_of_isAlgClosed
    hFixed hG.baseChange_toAlgebraicClosure hH.baseChange_toAlgebraicClosure
    ((GroupScheme.baseChange b).map i) (hi.baseChange b)
  rw [SubgroupFunctor.range_baseChangeHom]
  exact hn.baseChange b

section CenterMap

variable {k : Type u} [Field k]
    {G H ZG ZH : GroupScheme (Spec (CommRingCat.of k))}
    (hCenter : NormalReductiveCenterStatement.{u})
    (hG : IsConnectedReductive G) (hH : IsConnectedReductive H)
    (i : H ⟶ G) (hi : IsClosedSubgroup i)
    (hn : (SubgroupFunctor.range i).IsNormal)
    (zH : ZH ⟶ H) (hzH : IsSchemeTheoreticCenter zH)
    (zG : ZG ⟶ G) (hzG : IsSchemeTheoreticCenter zG)

/-- The actual map on chosen full-centre representatives induced by a closed
normal inclusion of connected reductive groups, under centre containment. -/
def normalCenterMap : ZH ⟶ ZG :=
  hzG.isRepresentedBy.factorHom (zH ≫ i) (by
    intro T x hx
    obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
    change y ≫ (zH ≫ i).hom.hom ∈ (center G).carrier T
    have h := hCenter k G H hG hH i hi hn T (hzH.isCentral T y)
    change (y ≫ zH.hom.hom) ≫ i.hom.hom ∈ (center G).carrier T at h
    rw [Grp.comp_hom_hom, ← Category.assoc]
    exact h)

/-- The induced centre map commutes with the given inclusions. -/
theorem normalCenterMap_comp :
    normalCenterMap hCenter hG hH i hi hn zH hzH zG hzG ≫ zG = zH ≫ i :=
  hzG.isRepresentedBy.factorHom_comp _ _

/-- The induced centre map is the unique map compatible with the inclusions. -/
theorem normalCenterMap_unique (f : ZH ⟶ ZG) (hf : f ≫ zG = zH ≫ i) :
    f = normalCenterMap hCenter hG hH i hi hn zH hzH zG hzG :=
  hzG.isRepresentedBy.factorHom_unique _ _ hf

/-- The map induced on full-centre representatives is a closed immersion. -/
theorem normalCenterMap_isClosedSubgroup :
    IsClosedSubgroup (normalCenterMap hCenter hG hH i hi hn zH hzH zG hzG) := by
  apply IsClosedSubgroup.of_comp hzG.1
  rw [normalCenterMap_comp]
  let : IsClosedImmersion zH.hom.hom.left := hzH.1
  let : IsClosedImmersion i.hom.hom.left := hi
  change IsClosedImmersion (zH.hom.hom.left ≫ i.hom.hom.left)
  infer_instance

end CenterMap

end Langlands.GroupScheme
