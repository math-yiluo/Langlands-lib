import Langlands.GroupScheme.IdentityComponentPowers
import Mathlib.GroupTheory.QuotientGroup.Defs

/-! # The finite quotient of rational points by identity-component points -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.IdentityComponent

variable {k : Type u} [Field k] (H : GroupScheme (Spec (CommRingCat.of k)))

/-- The component of the actual scheme point underlying a rational section. -/
def pointComponent (x : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ H.X) :
    _root_.ConnectedComponents H.X.left :=
  _root_.ConnectedComponents.mk (x.left (basePoint k))

@[simp]
theorem translationComponents_pointComponent
    (x y : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ H.X) :
    translationComponents H x (pointComponent H y) = pointComponent H (x * y) :=
  translationComponents_point H x y

variable [Smooth H.X.hom] [IsAffineHom H.X.hom]

/-- The subgroup of rational sections factoring through the actual identity component. -/
def rationalIdentitySubgroup :
    Subgroup (𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ H.X) :=
  (SubgroupFunctor.range (identityComponentι H)).carrier _

theorem mem_rationalIdentitySubgroup
    (x : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ H.X) :
    x ∈ rationalIdentitySubgroup H ↔
      ∃ y : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ (identityComponent H).X,
        y ≫ (identityComponentι H).hom.hom = x :=
  Iff.rfl

instance normal_rationalIdentitySubgroup : (rationalIdentitySubgroup H).Normal where
  conj_mem x hx g :=
    isNormal_range_identityComponentι H _ g x (Subgroup.mem_top g) hx

/-- Factoring through the open identity component is detected on the unique base point. -/
theorem mem_rationalIdentitySubgroup_iff
    (x : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ H.X) :
    x ∈ rationalIdentitySubgroup H ↔ pointComponent H x = pointComponent H 1 := by
  rw [mem_rationalIdentitySubgroup]
  change (∃ y, y ≫ (identityComponentι H).hom.hom = x) ↔
    _root_.ConnectedComponents.mk (x.left (basePoint k)) =
      _root_.ConnectedComponents.mk (identityPoint H)
  rw [_root_.ConnectedComponents.coe_eq_coe']
  constructor
  · rintro ⟨y, rfl⟩
    change (identityComponentι H).hom.hom.left (y.left (basePoint k)) ∈
      connectedComponent (identityPoint H)
    rw [← range_identityComponentι H]
    exact Set.mem_range_self _
  · intro hx
    have hrange : Set.range x.left ⊆ Set.range (identityComponentι H).hom.hom.left := by
      rw [range_identityComponentι H]
      rintro _ ⟨p, rfl⟩
      have hp : p = basePoint k :=
        @Subsingleton.elim (Spec (CommRingCat.of k)) _ p _
      simpa only [hp] using hx
    exact ⟨FiniteEtaleImage.liftOver (identityComponentι H).hom.hom x hrange,
      FiniteEtaleImage.liftOver_fac _ _ _⟩

/-- Two rational sections have the same scheme component precisely when their
quotient lies in the identity-component subgroup. -/
theorem pointComponent_eq_iff
    (x y : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ H.X) :
    pointComponent H x = pointComponent H y ↔ x⁻¹ * y ∈ rationalIdentitySubgroup H := by
  rw [mem_rationalIdentitySubgroup_iff]
  calc
    pointComponent H x = pointComponent H y ↔
        translationComponents H x⁻¹ (pointComponent H x) =
          translationComponents H x⁻¹ (pointComponent H y) :=
      (translationComponents H x⁻¹).injective.eq_iff.symm
    _ ↔ pointComponent H 1 = pointComponent H (x⁻¹ * y) := by
      rw [translationComponents_pointComponent, translationComponents_pointComponent,
        inv_mul_cancel]
    _ ↔ pointComponent H (x⁻¹ * y) = pointComponent H 1 := eq_comm

/-- The group quotient of rational points by the rational points of the actual
identity component. This is a quotient of groups, not a scheme quotient. -/
def RationalComponentQuotient :=
  (𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ H.X) ⧸ rationalIdentitySubgroup H

instance : Group (RationalComponentQuotient H) :=
  inferInstanceAs (Group (_ ⧸ rationalIdentitySubgroup H))

/-- The canonical quotient homomorphism on rational points. -/
def rationalComponentProjection :
    (𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ H.X) →* RationalComponentQuotient H :=
  QuotientGroup.mk' (rationalIdentitySubgroup H)

theorem rationalComponentProjection_surjective :
    Function.Surjective (rationalComponentProjection H) :=
  QuotientGroup.mk'_surjective _

@[simp]
theorem ker_rationalComponentProjection :
    (rationalComponentProjection H).ker = rationalIdentitySubgroup H :=
  QuotientGroup.ker_mk' _

/-- Embed the rational quotient into the connected components of the actual scheme. -/
def rationalComponentEmbedding :
    RationalComponentQuotient H ↪ _root_.ConnectedComponents H.X.left where
  toFun := Quotient.lift (pointComponent H) (by
    intro x y hxy
    exact (pointComponent_eq_iff H x y).mpr (QuotientGroup.leftRel_apply.mp hxy))
  inj' := by
    intro a b hab
    induction a using Quotient.inductionOn with
    | h x =>
      induction b using Quotient.inductionOn with
      | h y =>
        exact Quotient.sound (QuotientGroup.leftRel_apply.mpr
          ((pointComponent_eq_iff H x y).mp hab))

@[simp]
theorem rationalComponentEmbedding_projection
    (x : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ H.X) :
    rationalComponentEmbedding H (rationalComponentProjection H x) = pointComponent H x :=
  rfl

instance finite_rationalComponentQuotient : Finite (RationalComponentQuotient H) := by
  let := finite_connectedComponents H
  exact Finite.of_injective (rationalComponentEmbedding H) (rationalComponentEmbedding H).injective

/-- Every homomorphism killing the actual identity-component rational subgroup
factors through the rational quotient. -/
def rationalComponentLift {M : Type*} [Group M]
    (f : (𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ H.X) →* M)
    (hf : rationalIdentitySubgroup H ≤ f.ker) :
    RationalComponentQuotient H →* M :=
  QuotientGroup.lift (rationalIdentitySubgroup H) f hf

@[simp]
theorem rationalComponentLift_projection {M : Type*} [Group M]
    (f : (𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ H.X) →* M)
    (hf : rationalIdentitySubgroup H ≤ f.ker)
    (x : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ H.X) :
    rationalComponentLift H f hf (rationalComponentProjection H x) = f x :=
  rfl

theorem rationalComponentLift_unique {M : Type*} [Group M]
    (f : (𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ H.X) →* M)
    (hf : rationalIdentitySubgroup H ≤ f.ker)
    (g : RationalComponentQuotient H →* M)
    (hg : g.comp (rationalComponentProjection H) = f) :
    g = rationalComponentLift H f hf := by
  apply QuotientGroup.monoidHom_ext
  exact hg

end Langlands.GroupScheme.IdentityComponent
