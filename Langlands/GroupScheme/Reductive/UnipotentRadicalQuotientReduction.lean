import Langlands.GroupScheme.SubgroupIntersection
import Langlands.GroupScheme.Reductive.UnipotentRadical
import Langlands.GroupScheme.CentralIsogeny.Basic

/-! # Inverse images and the maximality argument for radical quotients -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace SubgroupPreimage

variable {S : Scheme.{u}} {G Q H : GroupScheme S} (q : G ⟶ Q) (j : H ⟶ Q)

/-- The actual inverse image of a subgroup homomorphism is a group-scheme pullback. -/
abbrev groupScheme : GroupScheme S := subgroupIntersection q j

/-- The projection of the inverse image to the ambient group. -/
abbrev inclusion : groupScheme q j ⟶ G := subgroupIntersectionFst q j

/-- The quotient homomorphism on the inverse image. -/
abbrev projection : groupScheme q j ⟶ H := subgroupIntersectionSnd q j

/-- Forgetting the group law retains the relative pullback. -/
theorem isPullback : IsPullback (inclusion q j).hom.hom (projection q j).hom.hom
    q.hom.hom j.hom.hom :=
  subgroupIntersection_isPullback q j

/-- The inverse-image square is a pullback of actual schemes. -/
theorem isPullback_scheme : IsPullback (inclusion q j).hom.hom.left
    (projection q j).hom.hom.left q.hom.hom.left j.hom.hom.left :=
  subgroupIntersection_isPullback_scheme q j

/-- Every test scheme sees precisely the inverse image of the given subgroup range. -/
theorem range_inclusion : SubgroupFunctor.range (inclusion q j) =
    (SubgroupFunctor.range j).comap q := by
  ext T x
  rw [SubgroupFunctor.mem_comap]
  constructor
  · rw [SubgroupFunctor.mem_range]
    rintro ⟨y, rfl⟩
    rw [SubgroupFunctor.mem_range]
    exact ⟨y ≫ (projection q j).hom.hom, by
      change (y ≫ (projection q j).hom.hom) ≫ j.hom.hom =
        (y ≫ (inclusion q j).hom.hom) ≫ q.hom.hom
      rw [Category.assoc, Category.assoc, (isPullback q j).w]⟩
  · rw [SubgroupFunctor.mem_range, SubgroupFunctor.mem_range]
    rintro ⟨y, hy⟩
    exact ⟨(isPullback q j).lift x y hy.symm, (isPullback q j).lift_fst _ _ _⟩

/-- The inverse image of an all-test normal subgroup is normal. -/
theorem isNormal (hj : (SubgroupFunctor.range j).IsNormal) :
    (SubgroupFunctor.range (inclusion q j)).IsNormal := by
  rw [range_inclusion]
  exact hj.comap q

/-- A closed subgroup has a closed actual inverse image. -/
theorem isClosedSubgroup (hj : IsClosedSubgroup j) :
    IsClosedSubgroup (inclusion q j) := by
  change IsClosedImmersion (inclusion q j).hom.hom.left
  change IsClosedImmersion j.hom.hom.left at hj
  exact MorphismProperty.of_isPullback (isPullback_scheme q j).flip hj

/-- Flatness of the quotient is preserved by inverse image. -/
theorem flat_projection [Flat q.hom.hom.left] : Flat (projection q j).hom.hom.left :=
  MorphismProperty.of_isPullback (isPullback_scheme q j) inferInstance

/-- Scheme surjectivity of the quotient is preserved by inverse image. -/
theorem surjective_projection [Surjective q.hom.hom.left] :
    Surjective (projection q j).hom.hom.left :=
  MorphismProperty.of_isPullback (isPullback_scheme q j) inferInstance

/-- A smooth quotient has a smooth inverse-image projection. -/
theorem smooth_projection [Smooth q.hom.hom.left] :
    Smooth (projection q j).hom.hom.left :=
  MorphismProperty.of_isPullback (isPullback_scheme q j) inferInstance

/-- Inverse images of smooth subgroups under a smooth quotient are smooth over the base. -/
theorem smooth [Smooth q.hom.hom.left] [Smooth H.X.hom] :
    Smooth (groupScheme q j).X.hom := by
  let : Smooth (projection q j).hom.hom.left := smooth_projection q j
  rw [← Over.w (projection q j).hom.hom]
  infer_instance

/-- Inverse images of closed subgroups in an affine group are affine over the base. -/
theorem isAffineHom [IsAffineHom G.X.hom] (hj : IsClosedSubgroup j) :
    IsAffineHom (groupScheme q j).X.hom := by
  let : IsClosedImmersion (inclusion q j).hom.hom.left := isClosedSubgroup q j hj
  rw [← Over.w (inclusion q j).hom.hom]
  infer_instance

/-- If an inverse image lies in the full kernel of a flat surjective quotient,
the original subgroup has trivial image on every test. -/
theorem range_eq_bot_of_range_inclusion_le_kernel
    [Flat q.hom.hom.left] [Surjective q.hom.hom.left]
    (h : SubgroupFunctor.range (inclusion q j) ≤ SubgroupFunctor.range (kernelι q)) :
    SubgroupFunctor.range j = ⊥ := by
  let : Flat (projection q j).hom.hom.left := flat_projection q j
  let : Surjective (projection q j).hom.hom.left := surjective_projection q j
  let : Epi (projection q j).hom.hom.left :=
    Flat.epi_of_flat_of_surjective (projection q j).hom.hom.left
  let : Epi (projection q j).hom.hom := Over.epi_of_epi_left _
  have hk : (inclusion q j).hom.hom ≫ q.hom.hom = 1 := by
    apply (mem_range_kernelι_iff q ((inclusion q j).hom.hom)).mp
    apply h (groupScheme q j).X
    rw [SubgroupFunctor.mem_range]
    exact ⟨𝟙 _, Category.id_comp _⟩
  have hjone : j.hom.hom = 1 := by
    apply (cancel_epi (projection q j).hom.hom).mp
    rw [← (isPullback q j).w, hk, MonObj.comp_one]
  ext T x
  rw [SubgroupFunctor.bot_carrier, Subgroup.mem_bot]
  constructor
  · rw [SubgroupFunctor.mem_range]
    rintro ⟨y, rfl⟩
    change y ≫ j.hom.hom = 1
    rw [hjone, MonObj.comp_one]
  · rintro rfl
    exact Subgroup.one_mem _

end SubgroupPreimage

section Radical

variable {k : Type u} [Field k]
    {G U Q : GroupScheme (Spec (CommRingCat.of k))}
    {i : U ⟶ G} (hi : IsUnipotentRadical i) (q : G ⟶ Q)
    [Flat q.hom.hom.left] [Surjective q.hom.hom.left]
    (hk : SubgroupFunctor.range (kernelι q) = SubgroupFunctor.range i)

include hi hk

/-- Radical maximality reduces quotient radical triviality to smooth connected
unipotence of the actual inverse images of candidate unipotent normal subgroups. -/
theorem IsUnipotentRadical.hasTrivialUnipotentRadical_of_preimages
    (hpre : ∀ (H : GroupScheme (Spec (CommRingCat.of k))) (j : H ⟶ Q),
      IsClosedSubgroup j → Smooth H.X.hom → ConnectedSpace H.X.left →
      IsUnipotent H → (SubgroupFunctor.range j).IsNormal →
      Smooth (SubgroupPreimage.groupScheme q j).X.hom ∧
        ConnectedSpace (SubgroupPreimage.groupScheme q j).X.left ∧
        IsUnipotent (SubgroupPreimage.groupScheme q j)) :
    HasTrivialUnipotentRadical Q := by
  intro H j hj hs hc hu hn
  obtain ⟨hps, hpc, hpu⟩ := hpre H j hj hs hc hu hn
  apply SubgroupPreimage.range_eq_bot_of_range_inclusion_le_kernel q j
  rw [hk]
  exact hi.greatest (SubgroupPreimage.groupScheme q j) (SubgroupPreimage.inclusion q j)
    (SubgroupPreimage.isClosedSubgroup q j hj) hps hpc hpu
    (SubgroupPreimage.isNormal q j hn)

end Radical

end Langlands.GroupScheme
