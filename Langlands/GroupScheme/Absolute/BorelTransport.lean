import Langlands.GroupScheme.Absolute.Borel
import Langlands.GroupScheme.RepresentedSubgroup

/-! # Changes of presentation and conjugation of Borel subgroups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
variable {B B' G G' : GroupScheme (Spec (CommRingCat.of k))}

/-- Solvability is invariant under an isomorphism of group schemes. -/
theorem IsSolvableGroupScheme.of_iso (h : IsSolvableGroupScheme B) (e : B' ≅ B) :
    IsSolvableGroupScheme B' := by
  let e' := (GroupScheme.baseChange (toAlgebraicClosure k)).mapIso e
  let φ := isoPointsEquiv e' (Over.mk (𝟙 (Spec (CommRingCat.of (AlgebraicClosure k)))))
  let : Group.IsSolvable
      (Over.mk (𝟙 (Spec (CommRingCat.of (AlgebraicClosure k)))) ⟶
        ((GroupScheme.baseChange (toAlgebraicClosure k)).obj B).X) := h
  exact Group.isSolvable_of_isSolvable_injective (f := φ.toMonoidHom) φ.injective

/-- Changing the source presentation preserves the Borel property. -/
theorem IsBorelSubgroup.iso_comp {i : B ⟶ G} (hi : IsBorelSubgroup i) (e : B' ≅ B) :
    IsBorelSubgroup (e.hom ≫ i) := by
  have : IsClosedImmersion i.hom.hom.left := hi.isClosedSubgroup
  have : IsIso e.hom.hom.hom.left :=
    (inferInstance : IsIso ((Over.forget _).mapIso ((Grp.forget _).mapIso e)).hom)
  have : Smooth B.X.hom := hi.smooth
  refine ⟨?_, ?_, ?_, hi.isSolvableGroupScheme.of_iso e, ?_⟩
  · change IsClosedImmersion (e.hom.hom.hom.left ≫ i.hom.hom.left)
    infer_instance
  · rw [← Over.w e.hom.hom.hom]
    infer_instance
  · exact (Scheme.homeoOfIso ((Over.forget _).mapIso
      ((Grp.forget _).mapIso e))).connectedSpace_iff.mpr hi.connectedSpace
  · intro C j f hj hsm hconn hsol hf
    have : IsIso (e.inv ≫ f) :=
      hi.maximal C j (e.inv ≫ f) hj hsm hconn hsol (by
        rw [Category.assoc, hf, Iso.inv_hom_id_assoc])
    have hfactor : f = e.hom ≫ (e.inv ≫ f) := by simp
    rw [hfactor]
    infer_instance

/-- Changing the ambient group by an isomorphism preserves the Borel property. -/
theorem IsBorelSubgroup.comp_iso {i : B ⟶ G} (hi : IsBorelSubgroup i) (e : G ≅ G') :
    IsBorelSubgroup (i ≫ e.hom) := by
  have : IsClosedImmersion i.hom.hom.left := hi.isClosedSubgroup
  have : IsIso e.hom.hom.hom.left :=
    (inferInstance : IsIso ((Over.forget _).mapIso ((Grp.forget _).mapIso e)).hom)
  have : IsIso e.inv.hom.hom.left :=
    (inferInstance : IsIso ((Over.forget _).mapIso ((Grp.forget _).mapIso e.symm)).hom)
  refine ⟨?_, hi.smooth, hi.connectedSpace, hi.isSolvableGroupScheme, ?_⟩
  · change IsClosedImmersion (i.hom.hom.left ≫ e.hom.hom.hom.left)
    infer_instance
  · intro C j f hj hsm hconn hsol hf
    have : IsClosedImmersion j.hom.hom.left := hj
    apply hi.maximal C (j ≫ e.inv) f
    · change IsClosedImmersion (j.hom.hom.left ≫ e.inv.hom.hom.left)
      infer_instance
    · exact hsm
    · exact hconn
    · exact hsol
    · rw [← Category.assoc, hf, Category.assoc, e.hom_inv_id, Category.comp_id]

/-- A Borel subgroup is unchanged by replacing its representing closed embedding. -/
theorem IsBorelSubgroup.of_range_eq {i : B ⟶ G} (hi : IsBorelSubgroup i)
    {i' : B' ⟶ G} (hi' : IsClosedSubgroup i')
    (h : SubgroupFunctor.range i = SubgroupFunctor.range i') : IsBorelSubgroup i' := by
  have : IsClosedImmersion i.hom.hom.left := hi.isClosedSubgroup
  have : IsClosedImmersion i'.hom.hom.left := hi'
  have : Mono i.hom.hom := Over.mono_of_mono_left _
  have : Mono i'.hom.hom := Over.mono_of_mono_left _
  let hr : (SubgroupFunctor.range i).IsRepresentedBy i := ⟨inferInstance, rfl⟩
  let hr' : (SubgroupFunctor.range i).IsRepresentedBy i' := ⟨inferInstance, h.symm⟩
  let e := hr.isoOfIsRepresentedBy hr'
  have he : e.hom ≫ i' = i := hr.isoOfIsRepresentedBy_hom_comp hr'
  have he' : e.inv ≫ i = i' := by rw [← he, Iso.inv_hom_id_assoc]
  have htransport := hi.iso_comp e.symm
  change IsBorelSubgroup (e.inv ≫ i) at htransport
  rwa [he'] at htransport

/-- The Borel property depends only on the represented subgroup functor. -/
theorem isBorelSubgroup_iff_of_range_eq {i : B ⟶ G} {i' : B' ⟶ G}
    (hi : IsClosedSubgroup i) (hi' : IsClosedSubgroup i')
    (h : SubgroupFunctor.range i = SubgroupFunctor.range i') :
    IsBorelSubgroup i ↔ IsBorelSubgroup i' :=
  ⟨fun hb => hb.of_range_eq hi' h, fun hb => hb.of_range_eq hi h.symm⟩

/-- The actual conjugating isomorphism supplied by a conjugated factorization
between two Borel embeddings. -/
def IsBorelSubgroup.conjugatingIsoOfFactor {i : B ⟶ G} {i' : B' ⟶ G}
    (hi : IsBorelSubgroup i) (hi' : IsBorelSubgroup i')
    (g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)
    (f : B ⟶ B') (hf : f ≫ i' = i ≫ (G.innerIso g).hom) : B ≅ B' := by
  have : IsIso f := (hi.comp_iso (G.innerIso g)).maximal B' i' f
    hi'.isClosedSubgroup hi'.smooth hi'.connectedSpace hi'.isSolvableGroupScheme hf
  exact asIso f

@[simp] theorem IsBorelSubgroup.conjugatingIsoOfFactor_hom
    {i : B ⟶ G} {i' : B' ⟶ G}
    (hi : IsBorelSubgroup i) (hi' : IsBorelSubgroup i')
    (g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)
    (f : B ⟶ B') (hf : f ≫ i' = i ≫ (G.innerIso g).hom) :
    (hi.conjugatingIsoOfFactor hi' g f hf).hom = f := rfl

/-- The constructed isomorphism satisfies the exact conjugacy equation. -/
theorem IsBorelSubgroup.conjugatingIsoOfFactor_hom_comp
    {i : B ⟶ G} {i' : B' ⟶ G}
    (hi : IsBorelSubgroup i) (hi' : IsBorelSubgroup i')
    (g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)
    (f : B ⟶ B') (hf : f ≫ i' = i ≫ (G.innerIso g).hom) :
    i ≫ (G.innerIso g).hom = (hi.conjugatingIsoOfFactor hi' g f hf).hom ≫ i' :=
  hf.symm

/-- Containment of a conjugated Borel in a Borel supplies the actual conjugating isomorphism. -/
theorem IsBorelSubgroup.exists_conjugatingIso_of_factor {i : B ⟶ G} {i' : B' ⟶ G}
    (hi : IsBorelSubgroup i) (hi' : IsBorelSubgroup i')
    (g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)
    (f : B ⟶ B') (hf : f ≫ i' = i ≫ (G.innerIso g).hom) :
    ∃ φ : B ≅ B', i ≫ (G.innerIso g).hom = φ.hom ≫ i' :=
  ⟨hi.conjugatingIsoOfFactor hi' g f hf,
    hi.conjugatingIsoOfFactor_hom_comp hi' g f hf⟩

end Langlands.GroupScheme
