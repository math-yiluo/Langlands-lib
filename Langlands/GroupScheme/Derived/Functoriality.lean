import Langlands.GroupScheme.Derived.Basic
import Langlands.GroupScheme.SubgroupIntersectionKernelComparison

/-! # Functoriality of the full derived subgroup -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {S : Scheme.{u}} {G H D E : GroupScheme S}

/-- Every group-scheme homomorphism carries the full derived subgroup into
the full derived subgroup of its target, on every test scheme. -/
theorem derivedSubgroup_le_comap (f : G ⟶ H) :
    derivedSubgroup G ≤ (derivedSubgroup H).comap f := by
  intro T x hx C i hi hc
  have hp : (SubgroupFunctor.range (subgroupIntersectionFst f i)).ContainsCommutators := by
    rw [range_subgroupIntersectionFst_eq_comap]
    intro U a b
    change (a * b * a⁻¹ * b⁻¹) ≫ f.hom.hom ∈
      (SubgroupFunctor.range i).carrier U
    simpa only [MonObj.mul_comp, GrpObj.inv_comp] using
      hc U (a ≫ f.hom.hom) (b ≫ f.hom.hom)
  have hpre := derivedSubgroup_le_range (subgroupIntersectionFst f i)
    (isClosedSubgroup_subgroupIntersectionFst f hi) hp T hx
  rwa [range_subgroupIntersectionFst_eq_comap] at hpre

/-- A full derived subgroup is carried to the target's full derived subgroup
by the underlying homomorphism on points. -/
theorem mem_derivedSubgroup_comp (f : G ⟶ H) {T : Over S} {x : T ⟶ G.X}
    (hx : x ∈ (derivedSubgroup G).carrier T) :
    x ≫ f.hom.hom ∈ (derivedSubgroup H).carrier T :=
  derivedSubgroup_le_comap f T hx

/-- The homomorphism induced by an actual group-scheme homomorphism on
supplied closed representatives of the full derived subgroups. -/
def IsDerivedSubgroup.map {d : D ⟶ G} {e : E ⟶ H}
    (hd : IsDerivedSubgroup d) (he : IsDerivedSubgroup e) (f : G ⟶ H) : D ⟶ E :=
  he.isRepresentedBy.factorHom (d ≫ f) (by
    intro T x hx
    obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
    change (y ≫ d.hom.hom) ≫ f.hom.hom ∈ (derivedSubgroup H).carrier T
    apply mem_derivedSubgroup_comp
    rw [← hd.2]
    exact SubgroupFunctor.mem_range.mpr ⟨y, rfl⟩)

/-- The induced map agrees with the original map after the inclusions. -/
@[reassoc]
theorem IsDerivedSubgroup.map_comp {d : D ⟶ G} {e : E ⟶ H}
    (hd : IsDerivedSubgroup d) (he : IsDerivedSubgroup e) (f : G ⟶ H) :
    hd.map he f ≫ e = d ≫ f :=
  he.isRepresentedBy.factorHom_comp _ _

/-- Every automorphism preserves the full derived subgroup, including on
nonreduced test schemes. -/
theorem derivedSubgroup_comap_iso (φ : G ≅ H) :
    (derivedSubgroup H).comap φ.hom = derivedSubgroup G := by
  apply le_antisymm
  · intro T x hx
    change x ≫ φ.hom.hom.hom ∈ (derivedSubgroup H).carrier T at hx
    have h := mem_derivedSubgroup_comp φ.inv hx
    simpa only [Category.assoc, ← Grp.comp_hom_hom, Iso.hom_inv_id,
      Grp.id_hom_hom, Category.comp_id] using h
  · exact derivedSubgroup_le_comap φ.hom

end Langlands.GroupScheme
