import Langlands.GroupScheme.HomogeneousCosetRelation
import Langlands.AlgebraicGeometry.SmoothEtaleSourceDescentProof
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent

/-! # Étaleness of a smooth quotient by an open subgroup -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.CartesianMonoidalCategory
open CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

namespace HomogeneousCosetRelation

variable {S : Scheme.{u}} {G H : GroupScheme S} (i : H ⟶ G)
    {Q : Over S} (q : G.X ⟶ Q)
    (hfib : ∀ (U : Over S) (g h : U ⟶ G.X),
      g ≫ q = h ≫ q ↔ g⁻¹ * h ∈ (SubgroupFunctor.range i).carrier U)

/-- Choose a right-coset arrow between points with the same quotient image. -/
def quotientArrow {U : Over S} (g h : U ⟶ G.X) (heq : g ≫ q = h ≫ q) :
    U ⟶ arrows i :=
  lift g (Classical.choose (SubgroupFunctor.mem_range.mp ((hfib U g h).mp heq)))

@[simp] theorem quotientArrow_source {U : Over S} (g h : U ⟶ G.X)
    (heq : g ≫ q = h ≫ q) :
    quotientArrow i q hfib g h heq ≫ source i = g :=
  lift_source i _ _

@[simp] theorem quotientArrow_target {U : Over S} (g h : U ⟶ G.X)
    (heq : g ≫ q = h ≫ q) :
    quotientArrow i q hfib g h heq ≫ target i = h := by
  rw [quotientArrow, lift_target,
    Classical.choose_spec (SubgroupFunctor.mem_range.mp ((hfib U g h).mp heq)),
    mul_inv_cancel_left]

include hfib in
/-- The actual coset relation is the inverse image of the quotient diagonal. -/
theorem isPullback_diagonal_of_fibers [Mono i.hom.hom] :
    IsPullback (source i ≫ q) (inclusion i) (lift (𝟙 Q) (𝟙 Q)) (q ⊗ₘ q) := by
  have hw : source i ≫ q = target i ≫ q := by
    apply (hfib _ _ _).mpr
    exact (exists_arrow_iff i _ _).mp ⟨𝟙 _, Category.id_comp _, Category.id_comp _⟩
  have eqfst (c : PullbackCone (lift (𝟙 Q) (𝟙 Q)) (q ⊗ₘ q)) :
      (c.snd ≫ fst G.X G.X) ≫ q = c.fst := by
    simpa only [Category.assoc, lift_fst, Category.comp_id, tensorHom_fst] using
      (congrArg (fun f => f ≫ fst Q Q) c.condition).symm
  have eqsnd (c : PullbackCone (lift (𝟙 Q) (𝟙 Q)) (q ⊗ₘ q)) :
      (c.snd ≫ snd G.X G.X) ≫ q = c.fst := by
    simpa only [Category.assoc, lift_snd, Category.comp_id, tensorHom_snd] using
      (congrArg (fun f => f ≫ snd Q Q) c.condition).symm
  refine ⟨⟨?_⟩, ⟨PullbackCone.IsLimit.mk _
    (fun c => quotientArrow i q hfib (c.snd ≫ fst G.X G.X)
      (c.snd ≫ snd G.X G.X) ((eqfst c).trans (eqsnd c).symm)) ?_ ?_ ?_⟩⟩
  · apply hom_ext
    · simp only [Category.assoc, lift_fst, Category.comp_id, tensorHom_fst]
      rw [← Category.assoc, inclusion_fst]
    · simp only [Category.assoc, lift_snd, Category.comp_id, tensorHom_snd]
      rw [← Category.assoc, inclusion_snd]
      exact hw
  · intro c
    rw [← Category.assoc, quotientArrow_source]
    exact eqfst c
  · intro c
    apply hom_ext
    · simp only [Category.assoc, inclusion_fst, quotientArrow_source]
    · simp only [Category.assoc, inclusion_snd, quotientArrow_target]
  · intro c m hm₁ hm₂
    apply arrow_unique i
    · have h := congrArg (fun f => f ≫ fst G.X G.X) hm₂
      simpa only [Category.assoc, inclusion_fst, quotientArrow_source] using h
    · have h := congrArg (fun f => f ≫ snd G.X G.X) hm₂
      simpa only [Category.assoc, inclusion_snd, quotientArrow_target] using h

/-- The canonical actual scheme isomorphism displaying the coset relation
as the pullback of the quotient diagonal. -/
def quotientDiagonalIso [Mono i.hom.hom] :
    (arrows i).left ≅
      pullback (lift (𝟙 Q) (𝟙 Q)).left (q ⊗ₘ q).left :=
  ((isPullback_diagonal_of_fibers i q hfib).map (Over.forget S)).isoPullback

end HomogeneousCosetRelation

/-- A smooth surjective quotient of a smooth group by an open subgroup is
étale over the base, provided its fibers are the actual all-test cosets. -/
theorem etale_of_open_subgroup_quotient {S : Scheme.{u}} {G H : GroupScheme S}
    (i : H ⟶ G) [Mono i.hom.hom] (hi : IsOpenImmersion i.hom.hom.left)
    {Q : Over S} (q : G.X ⟶ Q) [Smooth G.X.hom]
    [Smooth q.left] [Surjective q.left]
    (hfib : ∀ (U : Over S) (g h : U ⟶ G.X),
      g ≫ q = h ≫ q ↔ g⁻¹ * h ∈ (SubgroupFunctor.range i).carrier U) :
    Etale Q.hom := by
  have hrel : IsOpenImmersion (HomogeneousCosetRelation.inclusion i).left :=
    MorphismProperty.of_isPullback
      ((HomogeneousCosetRelation.inclusion_isPullback i).map (Over.forget S)) hi
  have hcover :
      (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation : MorphismProperty Scheme.{u})
        (q ⊗ₘ q).left := by
    exact MorphismProperty.pullbackMap
      (P := @Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation)
      ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
      ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
      (Over.w q).symm (Over.w q).symm
  have hdiag : IsOpenImmersion (lift (𝟙 Q) (𝟙 Q)).left :=
    MorphismProperty.of_isPullback_of_descendsAlong
      (P := @IsOpenImmersion) (Q := @Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation)
      ((HomogeneousCosetRelation.isPullback_diagonal_of_fibers i q hfib).map
        (Over.forget S)).flip hcover hrel
  have : IsOpenImmersion (pullback.diagonal Q.hom) := hdiag
  have : FormallyUnramified Q.hom := inferInstance
  have : Smooth (q.left ≫ Q.hom) := by
    rw [Over.w q]
    infer_instance
  have : Smooth Q.hom :=
    Langlands.AlgebraicGeometry.smooth_of_smooth_of_surjective_of_smooth_comp q.left Q.hom
  exact Etale.of_formallyUnramified_of_flat Q.hom

end Langlands.GroupScheme
