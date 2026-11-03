import Langlands.GroupScheme.Absolute.BorelTransport
import Langlands.GroupScheme.Absolute.ParabolicTransport
import Langlands.GroupScheme.Rational.MinimalParabolic
import Langlands.GroupScheme.Rational.SplitRankTransport

/-! # Ambient isomorphisms of Borel and minimal parabolic subgroups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace SubgroupFunctor

variable {S : Scheme.{u}} {H H' G G' : GroupScheme S}


/-- Transport an all-test subgroup functor through an ambient isomorphism. -/
def transport (e : G ≅ G') (F : SubgroupFunctor G) : SubgroupFunctor G' where
  carrier U := (F.carrier U).comap ((yonedaGrp.map e.inv).app (op U)).hom
  comp_mem a x hx := by
    change (a ≫ x) ≫ e.inv.hom.hom ∈ F.carrier _
    rw [Category.assoc]
    exact F.comp_mem a hx

@[simp] theorem mem_transport (e : G ≅ G') (F : SubgroupFunctor G)
    (U : Over S) (x : U ⟶ G'.X) :
    x ∈ (transport e F).carrier U ↔ x ≫ e.inv.hom.hom ∈ F.carrier U := Iff.rfl

/-- Transport through an ambient isomorphism and then its inverse is the identity. -/
@[simp] theorem transport_symm_transport (e : G ≅ G') (F : SubgroupFunctor G) :
    transport e.symm (transport e F) = F := by
  apply ext
  intro U
  apply Subgroup.ext
  intro x
  change ((x ≫ e.hom.hom.hom) ≫ e.inv.hom.hom ∈ F.carrier U) ↔ x ∈ F.carrier U
  rw [Category.assoc, ← Grp.comp_hom_hom, e.hom_inv_id]
  rfl

/-- Ambient transport preserves inclusion on all test schemes. -/
theorem transport_mono (e : G ≅ G') {F F' : SubgroupFunctor G} (h : F ≤ F') :
    transport e F ≤ transport e F' := by
  intro U x hx
  exact h U hx

/-- An ambient group-scheme isomorphism identifies the ordered sets of all-test
subgroup functors. -/
def ambientOrderIso (e : G ≅ G') : SubgroupFunctor G ≃o SubgroupFunctor G' where
  toFun := transport e
  invFun := transport e.symm
  left_inv := transport_symm_transport e
  right_inv := by
    intro F
    simpa using transport_symm_transport e.symm F
  map_rel_iff' := by
    intro F F'
    constructor
    · intro h
      change transport e F ≤ transport e F' at h
      simpa only [transport_symm_transport] using transport_mono e.symm h
    · exact transport_mono e

/-- Inclusion of all-test ranges is preserved by postcomposition. -/
theorem range_comp_mono {i : H ⟶ G} {j : H' ⟶ G}
    (h : range i ≤ range j) (f : G ⟶ G') : range (i ≫ f) ≤ range (j ≫ f) := by
  rintro U x ⟨y, rfl⟩
  obtain ⟨z, hz⟩ := h U (show y ≫ i.hom.hom ∈ (range i).carrier U from ⟨y, rfl⟩)
  change U ⟶ H.X at y
  change U ⟶ H'.X at z
  change z ≫ j.hom.hom = y ≫ i.hom.hom at hz
  refine ⟨z, ?_⟩
  change z ≫ (j.hom.hom ≫ f.hom.hom) = y ≫ (i.hom.hom ≫ f.hom.hom)
  simpa only [Category.assoc] using
    congrArg (fun a : U ⟶ G.X => a ≫ f.hom.hom) hz

/-- An ambient isomorphism preserves and reflects inclusion of all-test ranges. -/
theorem range_comp_iso_le_iff (i : H ⟶ G) (j : H' ⟶ G) (e : G ≅ G') :
    range (i ≫ e.hom) ≤ range (j ≫ e.hom) ↔ range i ≤ range j := by
  constructor
  · intro h
    simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using
      range_comp_mono h e.inv
  · exact fun h => range_comp_mono h e.hom

/-- An ambient isomorphism preserves and reflects equality of all-test ranges. -/
theorem range_comp_iso_eq_iff (i : H ⟶ G) (j : H' ⟶ G) (e : G ≅ G') :
    range (i ≫ e.hom) = range (j ≫ e.hom) ↔ range i = range j := by
  simp only [le_antisymm_iff, range_comp_iso_le_iff]

end SubgroupFunctor

variable {k : Type u} [Field k]
  {B P G G' : GroupScheme (Spec (CommRingCat.of k))}

/-- Borel structure is invariant under ambient group isomorphisms. -/
theorem IsBorelSubgroup.comp_iso_iff (i : B ⟶ G) (e : G ≅ G') :
    IsBorelSubgroup (i ≫ e.hom) ↔ IsBorelSubgroup i := by
  constructor
  · intro hi
    simpa using hi.comp_iso e.symm
  · exact fun hi => hi.comp_iso e

/-- Parabolic subgroups are preserved by isomorphisms of the ambient group. -/
theorem IsParabolicSubgroup.comp_iso {i : P ⟶ G} (hi : IsParabolicSubgroup i)
    (e : G ≅ G') : IsParabolicSubgroup (i ≫ e.hom) := by
  refine ⟨hi.isClosedSubgroup.comp_iso e, hi.smooth, ?_⟩
  obtain ⟨B, j, f, hj, hf⟩ := hi.exists_isBorelSubgroup
  let F := GroupScheme.baseChange (toAlgebraicClosure k)
  refine ⟨B, j ≫ F.map e.hom, f, hj.comp_iso (F.mapIso e), ?_⟩
  rw [F.map_comp, ← Category.assoc, hf]

/-- Parabolic structure is invariant under ambient group isomorphisms. -/
theorem IsParabolicSubgroup.comp_iso_iff (i : P ⟶ G) (e : G ≅ G') :
    IsParabolicSubgroup (i ≫ e.hom) ↔ IsParabolicSubgroup i := by
  constructor
  · intro hi
    simpa using hi.comp_iso e.symm
  · exact fun hi => hi.comp_iso e

/-- Minimal rational parabolics are preserved by ambient group isomorphisms. -/
theorem IsMinimalParabolicSubgroup.comp_iso {i : P ⟶ G}
    (hi : IsMinimalParabolicSubgroup i) (e : G ≅ G') :
    IsMinimalParabolicSubgroup (i ≫ e.hom) := by
  refine ⟨hi.1.comp_iso e, ?_⟩
  intro Q j hj hle
  have hle' : SubgroupFunctor.range (j ≫ e.inv) ≤ SubgroupFunctor.range i := by
    simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using
      SubgroupFunctor.range_comp_mono hle e.inv
  have heq := hi.2 Q (j ≫ e.inv) (hj.comp_iso e.symm) hle'
  apply le_antisymm hle
  have hreverse := SubgroupFunctor.range_comp_mono heq.ge e.hom
  simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using hreverse

/-- Minimal rational parabolic structure is invariant under ambient isomorphisms. -/
theorem IsMinimalParabolicSubgroup.comp_iso_iff (i : P ⟶ G) (e : G ≅ G') :
    IsMinimalParabolicSubgroup (i ≫ e.hom) ↔ IsMinimalParabolicSubgroup i := by
  constructor
  · intro hi
    simpa using hi.comp_iso e.symm
  · exact fun hi => hi.comp_iso e

end Langlands.GroupScheme
