import Langlands.GroupScheme.Absolute.CentralizerBorelIntersectionStatement
import Langlands.GroupScheme.Absolute.BorelTransport
import Langlands.GroupScheme.Dynamic.CentralizerRestriction
import Langlands.GroupScheme.Dynamic.SmoothProof
import Langlands.GroupScheme.Rational.TorusGeneratedEnvelope

/-! # Geometry of the centralizer intersection with a Borel -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {G M B : GroupScheme (Spec (CommRingCat.of k))}

namespace Dynamic

/-- Identify the actual intersection with the affine centralizer of the restricted cocharacter. -/
def centralizerIntersectionIso (b : B ⟶ G) [Mono b.hom.hom]
    [IsAffine B.X.left] (hb : IsClosedSubgroup b)
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    (hχ : SubgroupFunctor.range χ ≤ SubgroupFunctor.range b)
    (j : M ⟶ G) (hj : IsClosedSubgroup j)
    (hrep : (centralizer χ).IsRepresentedBy j) :
    subgroupIntersection j b ≅ Affine.centralizerScheme (restrictCocharacter b χ hχ) := by
  have hr : (centralizer (restrictCocharacter b χ hχ)).IsRepresentedBy
      (subgroupIntersectionSnd j b) :=
    isRepresentedBy_intersectionSnd b hb (restrictCocharacter b χ hχ) j hj (by
      rwa [restrictCocharacter_comp])
  exact hr.isoOfIsRepresentedBy (Affine.isRepresentedBy_centralizerHom _)

/-- The isomorphism respects the actual inclusion into the containing subgroup. -/
theorem centralizerIntersectionIso_hom_comp (b : B ⟶ G) [Mono b.hom.hom]
    [IsAffine B.X.left] (hb : IsClosedSubgroup b)
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    (hχ : SubgroupFunctor.range χ ≤ SubgroupFunctor.range b)
    (j : M ⟶ G) (hj : IsClosedSubgroup j)
    (hrep : (centralizer χ).IsRepresentedBy j) :
    (centralizerIntersectionIso b hb χ hχ j hj hrep).hom ≫
      Affine.centralizerHom (restrictCocharacter b χ hχ) = subgroupIntersectionSnd j b := by
  unfold centralizerIntersectionIso
  exact SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy_hom_comp _ _

end Dynamic

/-- The centralizer intersection with a Borel is closed in the ambient centralizer,
smooth, affine, and solvable; its ambient range is the actual intersection. -/
theorem IsBorelSubgroup.centralizer_intersection_properties
    [IsAffineHom G.X.hom] {b : B ⟶ G} (hb : IsBorelSubgroup b)
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    (hχ : SubgroupFunctor.range χ ≤ SubgroupFunctor.range b)
    (j : M ⟶ G) (hj : IsClosedSubgroup j)
    (hrep : (Dynamic.centralizer χ).IsRepresentedBy j) :
    IsClosedSubgroup (subgroupIntersectionFst j b) ∧
      Smooth (subgroupIntersection j b).X.hom ∧
      IsAffineHom (subgroupIntersection j b).X.hom ∧
      IsSolvableGroupScheme (subgroupIntersection j b) ∧
      SubgroupFunctor.range (subgroupIntersectionFst j b ≫ j) =
        SubgroupFunctor.range j ⊓ SubgroupFunctor.range b := by
  have : IsClosedImmersion b.hom.hom.left := hb.isClosedSubgroup
  have : Mono b.hom.hom := Over.mono_of_mono_left _
  have : Smooth B.X.hom := hb.smooth
  have : IsAffineHom B.X.hom := by
    rw [← Over.w b.hom.hom]
    infer_instance
  have hc : IsClosedSubgroup (subgroupIntersectionSnd j b) :=
    Dynamic.isClosedSubgroup_intersectionSnd j b hj
  have : IsClosedImmersion (subgroupIntersectionSnd j b).hom.hom.left := hc
  have : Mono (subgroupIntersectionSnd j b).hom.hom := Over.mono_of_mono_left _
  have hr : (Dynamic.centralizer (Dynamic.restrictCocharacter b χ hχ)).IsRepresentedBy
      (subgroupIntersectionSnd j b) :=
    Dynamic.isRepresentedBy_intersectionSnd b hb.isClosedSubgroup
      (Dynamic.restrictCocharacter b χ hχ) j hj (by
        rwa [Dynamic.restrictCocharacter_comp])
  refine ⟨?_, ?_, ?_, hb.isSolvableGroupScheme.of_mono (subgroupIntersectionSnd j b), ?_⟩
  · change IsClosedImmersion (subgroupIntersectionFst j b).hom.hom.left
    exact MorphismProperty.of_isPullback
      (subgroupIntersection_isPullback_scheme j b).flip
      (show IsClosedImmersion b.hom.hom.left from hb.isClosedSubgroup)
  · exact (dynamicSmooth k B (Dynamic.restrictCocharacter b χ hχ)
      (subgroupIntersection j b) (subgroupIntersectionSnd j b)).2.1 hr
  · rw [← Over.w (subgroupIntersectionSnd j b).hom.hom]
    infer_instance
  · exact range_subgroupIntersectionHom j b

/-- If the actual centralizer intersection is connected, the desired Borel-containment
conclusion is equivalent to Borel maximality of its first projection. -/
theorem IsBorelSubgroup.centralizer_intersection_borel_iff
    [IsAffineHom G.X.hom] {b : B ⟶ G} (hb : IsBorelSubgroup b)
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    (hχ : SubgroupFunctor.range χ ≤ SubgroupFunctor.range b)
    (j : M ⟶ G) (hj : IsClosedSubgroup j)
    (hrep : (Dynamic.centralizer χ).IsRepresentedBy j)
    (hconn : ConnectedSpace (subgroupIntersection j b).X.left) :
    IsBorelSubgroup (subgroupIntersectionFst j b) ↔
      ∃ (C : GroupScheme (Spec (CommRingCat.of k))) (c : C ⟶ M),
        IsBorelSubgroup c ∧ SubgroupFunctor.range (c ≫ j) ≤ SubgroupFunctor.range b := by
  obtain ⟨hclosed, hsm, _, hsol, hrange⟩ :=
    hb.centralizer_intersection_properties χ hχ j hj hrep
  constructor
  · intro hB
    refine ⟨subgroupIntersection j b, subgroupIntersectionFst j b, hB, ?_⟩
    rw [hrange]
    exact fun _ _ hx => hx.2
  · rintro ⟨C, c, hc, hcb⟩
    have : IsClosedImmersion b.hom.hom.left := hb.isClosedSubgroup
    have : Mono b.hom.hom := Over.mono_of_mono_left _
    let hr : (SubgroupFunctor.range b).IsRepresentedBy b := ⟨inferInstance, rfl⟩
    let fB : C ⟶ B := hr.factorHom (c ≫ j) hcb
    have hfB : fB ≫ b = c ≫ j := hr.factorHom_comp _ _
    let f : C ⟶ subgroupIntersection j b := pullback.lift c fB hfB.symm
    have hf : f ≫ subgroupIntersectionFst j b = c := pullback.lift_fst _ _ _
    have : IsIso f := hc.maximal _ _ f hclosed hsm hconn hsol hf
    have he : (asIso f).inv ≫ c = subgroupIntersectionFst j b := by
      rw [← hf]
      exact (asIso f).inv_hom_id_assoc _
    have htransport := hc.iso_comp (asIso f).symm
    change IsBorelSubgroup ((asIso f).inv ≫ c) at htransport
    rwa [he] at htransport

end Langlands.GroupScheme
