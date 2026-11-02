import Langlands.GroupScheme.ConjugacyBaseChange
import Langlands.GroupScheme.InnerAutomorphismHom

/-! # Rational conjugacy with an isomorphism of source groups -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {S : Scheme.{u}} {G G' H H' H'' P Q : GroupScheme S}

/-- Rational conjugacy of homomorphisms, allowing an isomorphism of their sources. -/
def SubgroupConjugate (i : H ⟶ G) (i' : H' ⟶ G) : Prop :=
  ∃ (g : Over.mk (𝟙 S) ⟶ G.X) (e : H ≅ H'),
    i ≫ (G.innerIso g).hom = e.hom ≫ i'

theorem subgroupConjugate_iff_exists_iso (i : H ⟶ G) (i' : H' ⟶ G) :
    SubgroupConjugate i i' ↔ ∃ e : H ≅ H', HomConjugate i (e.hom ≫ i') := by
  constructor
  · rintro ⟨g, e, h⟩
    exact ⟨e, g, h⟩
  · rintro ⟨e, g, h⟩
    exact ⟨g, e, h⟩

theorem SubgroupConjugate.refl (i : H ⟶ G) : SubgroupConjugate i i := by
  refine ⟨1, Iso.refl H, ?_⟩
  simp only [innerIso_one_hom, Iso.refl_hom, Category.comp_id, Category.id_comp]

theorem SubgroupConjugate.symm {i : H ⟶ G} {i' : H' ⟶ G}
    (h : SubgroupConjugate i i') : SubgroupConjugate i' i := by
  obtain ⟨e, he⟩ := (subgroupConjugate_iff_exists_iso i i').1 h
  apply (subgroupConjugate_iff_exists_iso i' i).2
  refine ⟨e.symm, ?_⟩
  simpa only [Iso.symm_hom, Iso.inv_hom_id_assoc] using he.symm.precomp e.inv

theorem SubgroupConjugate.trans {i : H ⟶ G} {i' : H' ⟶ G} {i'' : H'' ⟶ G}
    (h : SubgroupConjugate i i') (h' : SubgroupConjugate i' i'') :
    SubgroupConjugate i i'' := by
  obtain ⟨e, he⟩ := (subgroupConjugate_iff_exists_iso i i').1 h
  obtain ⟨e', he'⟩ := (subgroupConjugate_iff_exists_iso i' i'').1 h'
  apply (subgroupConjugate_iff_exists_iso i i'').2
  refine ⟨e ≪≫ e', ?_⟩
  simpa only [Iso.trans_hom, Category.assoc] using he.trans (he'.precomp e.hom)

/-- A morphism of ambient groups carries rational subgroup conjugacies to conjugacies. -/
theorem SubgroupConjugate.postcomp {i : H ⟶ G} {i' : H' ⟶ G}
    (h : SubgroupConjugate i i') (f : G ⟶ G') :
    SubgroupConjugate (i ≫ f) (i' ≫ f) := by
  obtain ⟨e, he⟩ := (subgroupConjugate_iff_exists_iso i i').1 h
  apply (subgroupConjugate_iff_exists_iso _ _).2
  exact ⟨e, by simpa only [Category.assoc] using he.postcomp f⟩

theorem SubgroupConjugate.comp_iso_iff (i : H ⟶ G) (i' : H' ⟶ G) (e : G ≅ G') :
    SubgroupConjugate (i ≫ e.hom) (i' ≫ e.hom) ↔ SubgroupConjugate i i' := by
  constructor
  · intro h
    simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using h.postcomp e.inv
  · exact fun h => h.postcomp e.hom

theorem SubgroupConjugate.iso_source (e : H ≅ H') (i' : H' ⟶ G) :
    SubgroupConjugate (e.hom ≫ i') i' := by
  refine ⟨1, e, ?_⟩
  rw [innerIso_one_hom, Category.comp_id]

theorem SubgroupConjugate.conjugate (i : H ⟶ G)
    (g : Over.mk (𝟙 S) ⟶ G.X) : SubgroupConjugate i (i ≫ (G.innerIso g).hom) := by
  exact ⟨g, Iso.refl H, (Category.id_comp _).symm⟩

/-- Conjugate overgroups reduce subgroup conjugacy to conjugacy inside one overgroup. -/
theorem SubgroupConjugate.of_overgroups
    (j : P ⟶ G) (j' : Q ⟶ G) (f : H ⟶ P) (f' : H' ⟶ Q)
    (g : Over.mk (𝟙 S) ⟶ G.X) (e : P ≅ Q)
    (hj : j ≫ (G.innerIso g).hom = e.hom ≫ j')
    (hf : SubgroupConjugate (f ≫ e.hom) f') :
    SubgroupConjugate (f ≫ j) (f' ≫ j') := by
  have h : SubgroupConjugate (f ≫ j) ((f ≫ e.hom) ≫ j') := by
    refine ⟨g, Iso.refl H, ?_⟩
    simpa only [Iso.refl_hom, Category.id_comp, Category.assoc] using
      congrArg (fun a => f ≫ a) hj
  exact h.trans (hf.postcomp j')

end Langlands.GroupScheme
