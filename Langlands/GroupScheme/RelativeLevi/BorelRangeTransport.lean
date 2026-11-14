import Langlands.GroupScheme.RelativeLevi.Borel
import Langlands.GroupScheme.Descent.QuasiSplitDatum
import Langlands.GroupScheme.RepresentedSubgroup

/-! # Relative Borel subgroups and equality of all-test ranges -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

variable {S : Scheme.{u}} {B B' G : GroupScheme S} {i : B ⟶ G}

/-- Relative Borelness is independent of a monic presentation of the same
subgroup functor on all test schemes. -/
theorem IsRelativeBorelSubgroup.of_range_eq (hi : IsRelativeBorelSubgroup i)
    {i' : B' ⟶ G} (hi' : Mono i'.hom.hom)
    (h : SubgroupFunctor.range i = SubgroupFunctor.range i') :
    IsRelativeBorelSubgroup i' := by
  let : Mono i.hom.hom := hi.isRelativeParabolicSubgroup.mono
  let : Mono i'.hom.hom := hi'
  let hr : (SubgroupFunctor.range i).IsRepresentedBy i := ⟨inferInstance, rfl⟩
  let hr' : (SubgroupFunctor.range i).IsRepresentedBy i' := ⟨inferInstance, h.symm⟩
  let e := hr.isoOfIsRepresentedBy hr'
  have he : e.hom ≫ i' = i := hr.isoOfIsRepresentedBy_hom_comp hr'
  have he' : e.inv ≫ i = i' := by rw [← he, Iso.inv_hom_id_assoc]
  have hf : ∀ s : S, IsGeometricBorelSubgroup (RelativeLevi.residueFiberHom i' s) := by
    intro s
    rw [← he']
    change IsGeometricBorelSubgroup
      ((GroupScheme.baseChange (S.fromSpecResidueField s)).map (e.inv ≫ i))
    rw [Functor.map_comp]
    exact (hi.residueFiber s).iso_comp
      ((GroupScheme.baseChange (S.fromSpecResidueField s)).mapIso e.symm)
  let : Smooth B.X.hom := hi.isRelativeParabolicSubgroup.smooth
  let : IsAffineHom B.X.hom := hi.isRelativeParabolicSubgroup.isAffineHom
  let : IsIso e.inv.hom.hom.left :=
    (inferInstance : IsIso
      ((Over.forget _).mapIso ((Grp.forget _).mapIso e)).inv)
  refine ⟨⟨?_, ?_, hi', fun s => (hf s).isParabolicSubgroup⟩, hf⟩
  · rw [← Over.w e.inv.hom.hom]
    infer_instance
  · rw [← Over.w e.inv.hom.hom]
    infer_instance

/-- Equality of all-test ranges preserves and reflects relative Borelness
between monic subgroup presentations. -/
theorem isRelativeBorelSubgroup_iff_of_range_eq {i' : B' ⟶ G}
    (hi : Mono i.hom.hom) (hi' : Mono i'.hom.hom)
    (h : SubgroupFunctor.range i = SubgroupFunctor.range i') :
    IsRelativeBorelSubgroup i ↔ IsRelativeBorelSubgroup i' :=
  ⟨fun hB => hB.of_range_eq hi' h, fun hB => hB.of_range_eq hi h.symm⟩

/-- Transfer actual relative Borel data to a specified monic presentation
with the same all-test subgroup functor. -/
def relativeBorelOfRangeEq (hi : IsRelativeBorelSubgroup i)
    (i' : B' ⟶ G) (hi' : Mono i'.hom.hom)
    (h : SubgroupFunctor.range i = SubgroupFunctor.range i') :
    {j : B' ⟶ G // IsRelativeBorelSubgroup j} :=
  ⟨i', hi.of_range_eq hi' h⟩

@[simp]
theorem relativeBorelOfRangeEq_val (hi : IsRelativeBorelSubgroup i)
    (i' : B' ⟶ G) (hi' : Mono i'.hom.hom)
    (h : SubgroupFunctor.range i = SubgroupFunctor.range i') :
    (relativeBorelOfRangeEq hi i' hi' h).val = i' := rfl

end Langlands.GroupScheme
