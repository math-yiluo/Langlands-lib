import Langlands.GroupScheme.RelativeIdentityComponent.UnitNeighbourhood
import Langlands.GroupScheme.RelativeIdentityComponent.FieldGeometry

/-! # Product images and residue-fibre comparisons -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeIdentityComponent

open Langlands.GroupScheme.FiniteEtaleImage (liftOver liftOver_fac)

variable {S S' : Scheme.{u}} (G : GroupScheme S) (b : S' ⟶ S)
  {P : Over S} (i : P ⟶ G.X)

/-- Multiply two copies of a test map after actual base change. -/
abbrev baseChangedProduct :
    (Over.pullback b).obj P ⊗ (Over.pullback b).obj P ⟶
      ((GroupScheme.baseChange b).obj G).X :=
  ((Over.pullback b).map i ⊗ₘ (Over.pullback b).map i) ≫
    μ[((GroupScheme.baseChange b).obj G).X]

/-- The comparison with base change of the original product is the monoidal comparison. -/
theorem baseChangedProduct_eq : baseChangedProduct G b i =
    Functor.LaxMonoidal.μ (Over.pullback b) P P ≫
      (Over.pullback b).map ((i ⊗ₘ i) ≫ μ[G.X]) := by
  change ((_ ⊗ₘ _) ≫
    (Functor.LaxMonoidal.μ (Over.pullback b) G.X G.X ≫
      (Over.pullback b).map μ[G.X])) = _
  rw [← Category.assoc, Functor.LaxMonoidal.μ_natural, Category.assoc, ← Functor.map_comp]

/-- The monoidal comparison is an isomorphism, so the two product maps have the same range. -/
theorem range_baseChangedProduct_map :
    Set.range (baseChangedProduct G b i).left =
      Set.range ((Over.pullback b).map ((i ⊗ₘ i) ≫ μ[G.X])).left := by
  let a := Functor.LaxMonoidal.μ (Over.pullback b) P P
  let : IsIso a.left := (Over.forget S').map_isIso a
  have ha : Function.Surjective a.left := a.left.homeomorph.surjective
  rw [baseChangedProduct_eq]
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨a.left t, rfl⟩
  · rintro ⟨t, rfl⟩
    obtain ⟨t', rfl⟩ := ha t
    exact ⟨t', rfl⟩

/-- The product image after base change is the inverse image of the original product image. -/
theorem range_baseChangedProduct :
    Set.range (baseChangedProduct G b i).left =
      pullback.fst G.X.hom b ⁻¹' Set.range (((i ⊗ₘ i) ≫ μ[G.X]).left) := by
  rw [range_baseChangedProduct_map]
  exact range_of_isPullback (overPullback_isPullback b ((i ⊗ₘ i) ≫ μ[G.X]))

section Field

variable {k : Type u} [Field k] (H : GroupScheme (Spec (CommRingCat.of k)))
  [Smooth H.X.hom]

/-- Products of two points of the raw field identity restriction stay in the identity component. -/
theorem range_fieldIdentityProduct_subset :
    Set.range (((fieldIdentityInclusion H ⊗ₘ fieldIdentityInclusion H) ≫ μ[H.X]).left) ⊆
      IdentityComponent.identitySet H := by
  have : ConnectedSpace (fieldIdentityOver H ⊗ fieldIdentityOver H).left := by
    change ConnectedSpace (pullback (fieldIdentityOver H).hom (fieldIdentityOver H).hom : Scheme.{u})
    infer_instance
  apply IdentityComponent.range_subset_identitySet H _
    (lift (fieldIdentityOne H) (fieldIdentityOne H))
  rw [lift_map_assoc]
  have he : fieldIdentityOne H ≫ fieldIdentityInclusion H = η[H.X] :=
    liftOver_fac _ _ _
  rw [he]
  have h := MonObj.lift_comp_one_left (𝟙 (𝟙_ (Over (Spec (CommRingCat.of k))))) η[H.X]
  simp only [Category.id_comp] at h
  exact h

/-- Multiplication preserves the identity component for the image of any test map. -/
theorem field_product_range_subset {Q : Over (Spec (CommRingCat.of k))}
    (j : Q ⟶ H.X) (hj : Set.range j.left ⊆ IdentityComponent.identitySet H) :
    Set.range (((j ⊗ₘ j) ≫ μ[H.X]).left) ⊆ IdentityComponent.identitySet H := by
  have hj' : Set.range j.left ⊆ Set.range (fieldIdentityInclusion H).left := by
    rw [range_fieldIdentityInclusion]
    exact hj
  let a := liftOver (fieldIdentityInclusion H) j hj'
  have ha : a ≫ fieldIdentityInclusion H = j := liftOver_fac _ _ _
  have hm : ((a ⊗ₘ a) ≫ (fieldIdentityInclusion H ⊗ₘ fieldIdentityInclusion H)) ≫ μ[H.X] =
      (j ⊗ₘ j) ≫ μ[H.X] := by
    rw [tensorHom_comp_tensorHom, ha]
  rintro z ⟨q, rfl⟩
  apply range_fieldIdentityProduct_subset H
  refine ⟨(a ⊗ₘ a).left q, ?_⟩
  exact congrArg (fun f : Q ⊗ Q ⟶ H.X => f.left q) hm

end Field

/-- Multiplication preserves the relative identity set for arbitrary test maps. -/
theorem product_range_subset_underlyingSet [Smooth G.X.hom]
    (hi : Set.range i.left ⊆ underlyingSet G) :
    Set.range (((i ⊗ₘ i) ≫ μ[G.X]).left) ⊆ underlyingSet G := by
  apply (inRelativeIdentityComponent_iff_range_subset G _).mp
  intro s
  change Set.range ((Over.pullback (S.fromSpecResidueField s)).map
    ((i ⊗ₘ i) ≫ μ[G.X])).left ⊆ _
  rw [← range_baseChangedProduct_map]
  have : Smooth (residueFiber G s).X.hom :=
    inferInstanceAs (Smooth (pullback.snd G.X.hom (S.fromSpecResidueField s)))
  exact field_product_range_subset (residueFiber G s) _
    ((inRelativeIdentityComponent_iff_range_subset G i).mpr hi s)

end Langlands.GroupScheme.RelativeIdentityComponent
