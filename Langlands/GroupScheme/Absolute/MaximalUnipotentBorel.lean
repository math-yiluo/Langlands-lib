import Langlands.GroupScheme.Absolute.MaximalUnipotent
import Langlands.GroupScheme.Absolute.UnipotentPart
import Langlands.GroupScheme.Absolute.SolvableSubgroupBorelContainmentProof
import Langlands.GroupScheme.Absolute.BorelConjugacyProof
import Langlands.GroupScheme.SchemeActionProperFixedFromAffine

/-! # Maximal unipotent subgroups are the unipotent parts of Borels -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {U V B G : GroupScheme (Spec (CommRingCat.of k))}

/-- An embedded subgroup which is the greatest unipotent subgroup of a Borel. -/
def IsBorelUnipotentSubgroup (i : U ⟶ G) : Prop :=
  ∃ (B : GroupScheme (Spec (CommRingCat.of k))) (b : B ⟶ G) (u : U ⟶ B),
    IsBorelSubgroup b ∧ IsUnipotentPart u ∧ u ≫ b = i

variable [IsAlgClosed k] [Smooth G.X.hom] [IsAffineHom G.X.hom]
  [ConnectedSpace G.X.left]

/-- A maximal smooth connected unipotent subgroup is the unipotent part of a Borel. -/
theorem IsMaximalUnipotentSubgroup.isBorelUnipotentSubgroup {i : U ⟶ G}
    (hi : IsMaximalUnipotentSubgroup i) : IsBorelUnipotentSubgroup i := by
  have : Smooth U.X.hom := hi.smooth
  have : ConnectedSpace U.X.left := hi.connectedSpace
  have : IsClosedImmersion i.hom.hom.left := hi.isClosedSubgroup
  have : IsAffineHom U.X.hom := by
    rw [← Over.w i.hom.hom]
    infer_instance
  obtain ⟨B, b, f, hb, hf⟩ := solvableSubgroupBorelContainment k G U i
    hi.isClosedSubgroup (isSolvableGroupScheme_of_isUnipotent hi.isUnipotent)
  have : Smooth B.X.hom := hb.smooth
  have : ConnectedSpace B.X.left := hb.connectedSpace
  have : IsClosedImmersion b.hom.hom.left := hb.isClosedSubgroup
  have : IsAffineHom B.X.hom := by
    rw [← Over.w b.hom.hom]
    infer_instance
  obtain ⟨V, v, hv⟩ := exists_isUnipotentPart B hb.isSolvableGroupScheme
  have hfc : IsClosedSubgroup f := IsClosedSubgroup.of_comp hb.isClosedSubgroup
    (by rwa [hf])
  have : IsClosedImmersion f.hom.hom.left := hfc
  have : IsClosedImmersion v.hom.hom.left := hv.isClosedSubgroup
  have : Mono f.hom.hom := Over.mono_of_mono_left _
  have : Mono v.hom.hom := Over.mono_of_mono_left _
  have hle := hv.greatest U f hfc hi.isUnipotent
  let t := SubgroupFunctor.factorOfRangeLE hle
  have ht : t ≫ v = f := SubgroupFunctor.factorOfRangeLE_comp hle
  have hvc : IsClosedSubgroup (v ≫ b) := by
    change IsClosedImmersion (v.hom.hom.left ≫ b.hom.hom.left)
    infer_instance
  have : IsIso t := hi.maximal V (v ≫ b) t hvc hv.smooth hv.connectedSpace hv.isUnipotent
    (by rw [← Category.assoc, ht, hf])
  have hpart := hv.iso_comp (asIso t)
  change IsUnipotentPart (t ≫ v) at hpart
  rw [ht] at hpart
  exact ⟨B, b, f, hb, hpart, hf⟩

/-- Conjugacy of actual maximal smooth connected unipotent subgroup embeddings. -/
theorem IsMaximalUnipotentSubgroup.exists_conjugatingIso {i : U ⟶ G} {j : V ⟶ G}
    (hi : IsMaximalUnipotentSubgroup i) (hj : IsMaximalUnipotentSubgroup j) :
    ∃ (g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) (e : U ≅ V),
      i ≫ (G.innerIso g).hom = e.hom ≫ j := by
  obtain ⟨B, b, u, hb, hu, hiu⟩ := hi.isBorelUnipotentSubgroup
  obtain ⟨C, c, v, hc, hv, hjv⟩ := hj.isBorelUnipotentSubgroup
  obtain ⟨g, e, he⟩ := (borelConjugacy k G).2 B C b c hb hc
  obtain ⟨f, hf⟩ := (hu.comp_iso e).exists_iso hv
  refine ⟨g, f, ?_⟩
  rw [← hiu, Category.assoc, he, ← Category.assoc, ← hf, Category.assoc, hjv]

/-- The unipotent part of every Borel is maximal in the whole group. -/
theorem IsUnipotentPart.isMaximalUnipotentSubgroup {b : B ⟶ G} {u : U ⟶ B}
    (hu : IsUnipotentPart u) (hb : IsBorelSubgroup b) :
    IsMaximalUnipotentSubgroup (u ≫ b) := by
  obtain ⟨V, j, hj⟩ := MaximalUnipotentExistence.exists_maximal G
  obtain ⟨C, c, v, hc, hv, hjv⟩ := hj.isBorelUnipotentSubgroup
  obtain ⟨g, e, he⟩ := (borelConjugacy k G).2 C B c b hc hb
  obtain ⟨f, hf⟩ := (hv.comp_iso e).exists_iso hu
  have hconj : j ≫ (G.innerIso g).hom = f.hom ≫ (u ≫ b) := by
    rw [← hjv, Category.assoc, he, ← Category.assoc, ← hf, Category.assoc]
  have hmax := hj.comp_iso (G.innerIso g)
  rw [hconj] at hmax
  have hmax' := hmax.iso_comp f.symm
  simpa only [Iso.symm_hom, Iso.inv_hom_id_assoc] using hmax'

/-- Milne 17.14, with actual Borel and subgroup factorizations. -/
theorem isMaximalUnipotentSubgroup_iff_isBorelUnipotentSubgroup (i : U ⟶ G) :
    IsMaximalUnipotentSubgroup i ↔ IsBorelUnipotentSubgroup i := by
  refine ⟨fun hi => hi.isBorelUnipotentSubgroup, ?_⟩
  rintro ⟨B, b, u, hb, hu, rfl⟩
  exact hu.isMaximalUnipotentSubgroup hb

end Langlands.GroupScheme
