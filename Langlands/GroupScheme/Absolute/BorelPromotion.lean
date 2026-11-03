import Langlands.GroupScheme.Absolute.BorelTransport
import Langlands.GroupScheme.Torus.MaximalTransport

/-! # Promotion of Borels from closed overgroups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {B B' P G H : GroupScheme (Spec (CommRingCat.of k))}

/-- An ambient Borel is a Borel in each closed overgroup through which it factors. -/
theorem IsBorelSubgroup.of_comp {b : B ⟶ P} {i : P ⟶ G}
    (hi : IsClosedSubgroup i) (hb : IsBorelSubgroup (b ≫ i)) :
    IsBorelSubgroup b := by
  refine ⟨IsClosedSubgroup.of_comp hi hb.isClosedSubgroup,
    hb.smooth, hb.connectedSpace, hb.isSolvableGroupScheme, ?_⟩
  intro C c f hc hsm hconn hsol hf
  exact hb.maximal C (c ≫ i) f (hc.comp hi) hsm hconn hsol
    (by rw [← Category.assoc, hf])

/-- Rational conjugacy preserves the Borel property. -/
theorem IsBorelSubgroup.of_subgroupConjugate {b : B ⟶ G} {b' : B' ⟶ G}
    (hb : IsBorelSubgroup b) (h : SubgroupConjugate b b') :
    IsBorelSubgroup b' := by
  obtain ⟨g, e, he⟩ := h
  have hb' : IsBorelSubgroup (e.hom ≫ b') := by
    rw [← he]
    exact hb.comp_iso (G.innerIso g)
  simpa only [Iso.symm_hom, Iso.inv_hom_id_assoc] using hb'.iso_comp e.symm

/-- Conjugate embeddings are Borels together. -/
theorem SubgroupConjugate.isBorelSubgroup_iff {b : B ⟶ G} {b' : B' ⟶ G}
    (h : SubgroupConjugate b b') : IsBorelSubgroup b ↔ IsBorelSubgroup b' :=
  ⟨fun hb => hb.of_subgroupConjugate h,
    fun hb' => hb'.of_subgroupConjugate h.symm⟩

/-- Every two Borels of this group are conjugate by a point over the base field. -/
def BorelSubgroupsAreConjugate (G : GroupScheme (Spec (CommRingCat.of k))) : Prop :=
  ∀ (B B' : GroupScheme (Spec (CommRingCat.of k))) (b : B ⟶ G) (b' : B' ⟶ G),
    IsBorelSubgroup b → IsBorelSubgroup b' → SubgroupConjugate b b'

/-- Conjugacy of Borels is preserved by ambient group isomorphisms. -/
theorem BorelSubgroupsAreConjugate.of_iso
    (hG : BorelSubgroupsAreConjugate G) (e : G ≅ H) :
    BorelSubgroupsAreConjugate H := by
  intro B B' b b' hb hb'
  have hc := hG B B' (b ≫ e.inv) (b' ≫ e.inv)
    (hb.comp_iso e.symm) (hb'.comp_iso e.symm)
  simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using hc.postcomp e.hom

/-- If a closed overgroup has conjugate Borels and contains one ambient Borel,
then all of its Borels are ambient Borels. -/
theorem BorelSubgroupsAreConjugate.isBorelSubgroup_comp
    (hP : BorelSubgroupsAreConjugate P) (i : P ⟶ G) (hi : IsClosedSubgroup i)
    {b : B ⟶ P} (hb : IsBorelSubgroup b)
    (hex : ∃ (B' : GroupScheme (Spec (CommRingCat.of k))) (b' : B' ⟶ P),
      IsBorelSubgroup (b' ≫ i)) : IsBorelSubgroup (b ≫ i) := by
  obtain ⟨B', b', hb'⟩ := hex
  have hc := hP B B' b b' hb (IsBorelSubgroup.of_comp hi hb')
  exact (hc.postcomp i).isBorelSubgroup_iff.mpr hb'

end Langlands.GroupScheme
