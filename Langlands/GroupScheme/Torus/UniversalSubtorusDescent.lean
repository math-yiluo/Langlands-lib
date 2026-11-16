import Langlands.GroupScheme.Torus.UniversalSubtorusTransport
import Langlands.GroupScheme.Torus.FppfRelativeTorusDescent
import Langlands.GroupScheme.SubgroupFunctor.CoverMatching
import Langlands.GroupScheme.SubgroupFunctor.FppfLocality

/-! # Fppf descent of universal subtori -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

namespace IsUniversalSubtorus

/-- Universality of a closed relative torus can be checked on an fppf base cover. -/
theorem of_fppfCover {S : Scheme.{u}} {T H : GroupScheme S} {j : T ⟶ H}
    (𝒰 : Scheme.Cover.{u} Scheme.fppfPrecoverage S)
    (hj : IsClosedSubgroup j)
    (h : ∀ i, IsUniversalSubtorus ((GroupScheme.baseChange (𝒰.f i)).map j)) :
    IsUniversalSubtorus j := by
  have hT : RelativeTorus.IsTorus T :=
    .of_fppfCover 𝒰 (fun i => (h i).2.1)
  refine ⟨hj, hT, ?_⟩
  intro S' b T' f hT'
  let 𝒱 := 𝒰.pullback₁ b
  let F := GroupScheme.baseChange b
  have hloc (i : 𝒱.I₀) :
      IsUniversalSubtorus ((GroupScheme.baseChange (𝒱.f i)).map (F.map j)) := by
    let c := pullback.fst b (𝒰.f i)
    let d := pullback.snd b (𝒰.f i)
    let eT := Descent.squareComparison b c (𝒰.f i) d pullback.condition T
    let eH := Descent.squareComparison b c (𝒰.f i) d pullback.condition H
    have hn :
        (GroupScheme.baseChange c).map (F.map j) ≫ eH.hom =
          eT.hom ≫ (GroupScheme.baseChange d).map
            ((GroupScheme.baseChange (𝒰.f i)).map j) :=
      Descent.squareComparison_naturality _ _ _ _ _ j
    have hu := (((h i).baseChange d).comp_iso eH.symm).iso_comp eT
    have he :
        eT.hom ≫ ((GroupScheme.baseChange d).map
            ((GroupScheme.baseChange (𝒰.f i)).map j) ≫ eH.inv) =
          (GroupScheme.baseChange c).map (F.map j) := by
      rw [← Category.assoc, ← hn, Category.assoc, eH.hom_inv_id, Category.comp_id]
    simp only [Iso.symm_hom] at hu
    rw [he] at hu
    exact hu
  have hj' := hj.baseChange b
  let : Mono (F.map j).hom.hom := hj'.mono_overHom
  have hr : SubgroupFunctor.range f ≤ SubgroupFunctor.range (F.map j) := by
    apply (SubgroupFunctor.le_range_iff_baseChange_fppfCover 𝒱 (F.map j)).mpr
    intro i
    rw [← SubgroupFunctor.range_baseChangeHom, ← SubgroupFunctor.range_baseChangeHom]
    exact (hloc i).range_le
      ((GroupScheme.baseChange (𝒱.f i)).map f) (hT'.baseChange (𝒱.f i))
  have hrep : (SubgroupFunctor.range (F.map j)).IsRepresentedBy (F.map j) :=
    ⟨inferInstance, rfl⟩
  exact ⟨hrep.factorHom f hr, hrep.factorHom_comp f hr⟩

end IsUniversalSubtorus

namespace UniversalSubtorusDescent

variable {S : Scheme.{u}} {H : GroupScheme S}
    (𝒰 : Scheme.Cover.{u} Scheme.fppfPrecoverage S)
    (N : ∀ i, GroupScheme (𝒰.X i))
    (r : ∀ i, N i ⟶ (GroupScheme.baseChange (𝒰.f i)).obj H)
    (hr : ∀ i, IsUniversalSubtorus (r i))

include hr in
theorem matching :
    SubgroupFunctor.CoverDescent.IsMatching 𝒰 (fun i => SubgroupFunctor.range (r i)) := by
  apply SubgroupFunctor.CoverDescent.isMatching_of_overlap_range_eq 𝒰 N r
  intro i j
  exact ((hr i).baseChange (pullback.fst (𝒰.f i) (𝒰.f j))).range_eq
    (((hr j).baseChange (pullback.snd (𝒰.f i) (𝒰.f j))).comp_iso
      (SubgroupFunctor.CoverDescent.overlapSquareIso 𝒰 i j H).symm)

/-- The closed group representing the compatible local universal-subtorus ranges. -/
def representative :
    SubgroupFunctor.ClosedRepresentative
      (SubgroupFunctor.CoverDescent.subgroup 𝒰
        (fun i => SubgroupFunctor.range (r i))) :=
  SubgroupFunctor.CoverDescent.closedRepresentativeFppf 𝒰
    (fun i => SubgroupFunctor.range (r i)) (matching 𝒰 N r hr)
    (fun i => ⟨N i, r i, ⟨(hr i).1.mono_overHom, rfl⟩, (hr i).1⟩)

theorem localUniversal (i : 𝒰.I₀) :
    IsUniversalSubtorus
      ((GroupScheme.baseChange (𝒰.f i)).map (representative 𝒰 N r hr).hom) := by
  let C := representative 𝒰 N r hr
  have hrep :
      (SubgroupFunctor.range (r i)).IsRepresentedBy
        ((GroupScheme.baseChange (𝒰.f i)).map C.hom) := by
    have he := C.represents.baseChange (𝒰.f i)
    rw [SubgroupFunctor.CoverDescent.baseChange_subgroup 𝒰
      (fun i => SubgroupFunctor.range (r i)) (matching 𝒰 N r hr) i] at he
    exact he
  have hri : (SubgroupFunctor.range (r i)).IsRepresentedBy (r i) :=
    ⟨(hr i).1.mono_overHom, rfl⟩
  let e := hrep.isoOfIsRepresentedBy hri
  have he : e.hom ≫ r i = (GroupScheme.baseChange (𝒰.f i)).map C.hom :=
    hrep.isoOfIsRepresentedBy_hom_comp hri
  rw [← he]
  exact (hr i).iso_comp e

theorem universal : IsUniversalSubtorus (representative 𝒰 N r hr).hom :=
  IsUniversalSubtorus.of_fppfCover 𝒰 (representative 𝒰 N r hr).closed
    (localUniversal 𝒰 N r hr)

end UniversalSubtorusDescent

end Langlands.GroupScheme
