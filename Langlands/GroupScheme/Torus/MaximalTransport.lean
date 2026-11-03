import Langlands.GroupScheme.Torus.Maximal
import Langlands.GroupScheme.Rational.SplitRankTransport
import Langlands.GroupScheme.Rational.LeviFactorization
import Langlands.GroupScheme.Rational.SubgroupConjugacy

/-! # Transport of maximal tori and maximality inside closed subgroups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
variable {G G' H : GroupScheme (Spec (CommRingCat.of k))}
variable {T T' : CommGroupScheme (Spec (CommRingCat.of k))}

/-- Being a torus is preserved by an isomorphism of group schemes. -/
theorem IsTorus.of_iso (e : G ≅ H) (h : IsTorus H) : IsTorus G := by
  obtain ⟨K, hK, aK, h⟩ := h
  let := hK
  let := aK
  exact ⟨K, hK, aK,
    IsSplitTorus.of_iso
      ((GroupScheme.baseChange
        (Spec.map (CommRingCat.ofHom (algebraMap k K)))).mapIso e) h⟩

/-- The torus predicate is invariant under an isomorphism of group schemes. -/
theorem IsTorus.iso_iff (e : G ≅ H) : IsTorus G ↔ IsTorus H :=
  ⟨IsTorus.of_iso e.symm, IsTorus.of_iso e⟩

/-- Ambient group isomorphisms preserve maximal tori. -/
theorem IsMaximalTorus.comp_iso {i : T.toGrp ⟶ G}
    (hi : IsMaximalTorus i) (e : G ≅ G') : IsMaximalTorus (i ≫ e.hom) := by
  refine ⟨hi.1, hi.2.1.comp_iso e, ?_⟩
  intro T' i' f hT' hi' hf
  apply hi.2.2 T' (i' ≫ e.inv) f hT' (hi'.comp_iso e.symm)
  simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using
    congrArg (fun a => a ≫ e.inv) hf

/-- Maximality is invariant under an isomorphism of the ambient group. -/
theorem IsMaximalTorus.comp_iso_iff (i : T.toGrp ⟶ G) (e : G ≅ G') :
    IsMaximalTorus (i ≫ e.hom) ↔ IsMaximalTorus i := by
  constructor
  · intro hi
    simpa only [Category.assoc, Iso.symm_hom, Iso.hom_inv_id, Category.comp_id] using
      hi.comp_iso e.symm
  · exact fun hi => hi.comp_iso e

/-- Replacing the source torus by an isomorphic group preserves maximality. -/
theorem IsMaximalTorus.iso_comp (e : T'.toGrp ≅ T.toGrp) {i : T.toGrp ⟶ G}
    (hi : IsMaximalTorus i) : IsMaximalTorus (e.hom ≫ i) := by
  refine ⟨IsTorus.of_iso e hi.1, hi.2.1.iso_comp e, ?_⟩
  intro T'' i' f hT'' hi' hf
  have heq : (e.inv ≫ f) ≫ i' = i := by
    simpa only [Category.assoc, Iso.inv_hom_id_assoc] using
      congrArg (fun a => e.inv ≫ a) hf
  have : IsIso (e.inv ≫ f) := hi.2.2 T'' i' (e.inv ≫ f) hT'' hi' heq
  have : IsIso (e.hom ≫ (e.inv ≫ f)) := inferInstance
  simpa only [Iso.hom_inv_id_assoc] using this

/-- Maximality is invariant under an isomorphism of the source torus. -/
theorem IsMaximalTorus.iso_comp_iff (e : T'.toGrp ≅ T.toGrp) (i : T.toGrp ⟶ G) :
    IsMaximalTorus (e.hom ≫ i) ↔ IsMaximalTorus i := by
  constructor
  · intro hi
    simpa only [Iso.symm_hom, Iso.inv_hom_id_assoc] using hi.iso_comp e.symm
  · exact fun hi => hi.iso_comp e

/-- An ambient maximal torus is maximal in every closed subgroup through which it factors. -/
theorem IsMaximalTorus.of_comp {f : T.toGrp ⟶ H} {j : H ⟶ G}
    (hj : IsClosedSubgroup j) (hf : IsMaximalTorus (f ≫ j)) : IsMaximalTorus f := by
  refine ⟨hf.1, IsClosedSubgroup.of_comp hj hf.2.1, ?_⟩
  intro T' i' a hT' hi' ha
  apply hf.2.2 T' (i' ≫ j) a hT' (hi'.comp hj)
  simpa only [Category.assoc] using congrArg (fun b => b ≫ j) ha

/-- Conjugate torus embeddings have equivalent maximality predicates. -/
theorem SubgroupConjugate.isMaximalTorus_iff {i : T.toGrp ⟶ G} {i' : T'.toGrp ⟶ G}
    (h : SubgroupConjugate i i') : IsMaximalTorus i ↔ IsMaximalTorus i' := by
  obtain ⟨g, e, he⟩ := h
  calc
    IsMaximalTorus i ↔ IsMaximalTorus (i ≫ (G.innerIso g).hom) :=
      (IsMaximalTorus.comp_iso_iff i (G.innerIso g)).symm
    _ ↔ IsMaximalTorus (e.hom ≫ i') := by rw [he]
    _ ↔ IsMaximalTorus i' := IsMaximalTorus.iso_comp_iff e i'

/-- Any two maximal tori of this group are conjugate by a point over the base field. -/
def MaximalToriAreConjugate (G : GroupScheme (Spec (CommRingCat.of k))) : Prop :=
  ∀ (T T' : CommGroupScheme (Spec (CommRingCat.of k)))
    (i : T.toGrp ⟶ G) (i' : T'.toGrp ⟶ G),
    IsMaximalTorus i → IsMaximalTorus i' → SubgroupConjugate i i'

/-- Conjugacy of maximal tori is preserved by ambient group isomorphisms. -/
theorem MaximalToriAreConjugate.of_iso (hG : MaximalToriAreConjugate G) (e : G ≅ H) :
    MaximalToriAreConjugate H := by
  intro T T' i i' hi hi'
  have h := hG T T' (i ≫ e.inv) (i' ≫ e.inv)
    (hi.comp_iso e.symm) (hi'.comp_iso e.symm)
  simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using h.postcomp e.hom

/-- Inside a closed subgroup with conjugate maximal tori, one ambient maximal torus
certifies ambient maximality of every maximal torus of that subgroup. -/
theorem MaximalToriAreConjugate.isMaximalTorus_comp
    (hH : MaximalToriAreConjugate H) (j : H ⟶ G) (hj : IsClosedSubgroup j)
    {f : T.toGrp ⟶ H} (hf : IsMaximalTorus f)
    (hex : ∃ (T' : CommGroupScheme (Spec (CommRingCat.of k)))
      (f' : T'.toGrp ⟶ H), IsMaximalTorus (f' ≫ j)) :
    IsMaximalTorus (f ≫ j) := by
  obtain ⟨T', f', hf'⟩ := hex
  have hc := hH T T' f f' hf (IsMaximalTorus.of_comp hj hf')
  exact (hc.postcomp j).isMaximalTorus_iff.mpr hf'

end Langlands.GroupScheme
