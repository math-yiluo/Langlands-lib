import Langlands.GroupScheme.Descent.DisjointComponentHoms
import Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_IsZariskiLocalAtTarget_sigmaMap

/-! # Gluing group schemes over an arbitrary disjoint decomposition -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.Descent.DisjointGroupGluing

variable {I : Type u} {S : Scheme.{u}} {Z : I → Scheme.{u}}
  (p : ∀ i, Z i ⟶ S) [IsIso (Sigma.desc p)] (H : ∀ i, GroupScheme (Z i))

attribute [local instance] DisjointComponents.pointwiseCartesianMonoidalCategory

/-- The disjoint union of the underlying schemes, over the decomposed base. -/
def underlying : Over S :=
  Over.mk (Sigma.desc fun i => (H i).X.hom ≫ p i)

omit [IsIso (Sigma.desc p)] in
/-- The structure map of the disjoint union factors through the disjoint union of the
bases. -/
theorem underlying_hom :
    (underlying p H).hom = Limits.Sigma.map (fun i => (H i).X.hom) ≫ Sigma.desc p := by
  refine Sigma.hom_ext _ _ fun i => ?_
  simp [underlying]

/-- A component of the glued underlying scheme is a genuine pullback. -/
theorem component_isPullback (i : I) :
    IsPullback (Sigma.ι (fun j => (H j).X.left) i) (H i).X.hom
      (underlying p H).hom (p i) := by
  have s := (P2MW.S_AlgebraicGeometry_IsZariskiLocalAtTarget_sigmaMap.AlgebraicGeometry.SigmaMapU4.isPullback_sigmaι_sigmaMap
    (fun j => (H j).X.hom) i).flip
  have t : IsPullback (Sigma.ι Z i) (𝟙 (Z i)) (Sigma.desc p) (p i) :=
    IsPullback.of_vert_isIso ⟨by simp⟩
  have h := s.paste_vert t
  rw [Category.comp_id, ← underlying_hom] at h
  exact h

/-- The original relative component, recovered by actual slice pullback. -/
def componentUnderlyingIso (i : I) :
    (Over.pullback (p i)).obj (underlying p H) ≅ (H i).X :=
  Over.isoMk (component_isPullback p H i).isoPullback.symm (by simp)

/-- Pointwise group laws on the family of relative schemes. -/
@[instance_reducible] def familyGrpObj : GrpObj (fun i => (H i).X) where
  one i := η[(H i).X]
  mul i := μ[(H i).X]
  inv i := ι[(H i).X]
  one_mul := by funext i; exact MonObj.one_mul (H i).X
  mul_one := by funext i; exact MonObj.mul_one (H i).X
  mul_assoc := by funext i; exact MonObj.mul_assoc (H i).X
  left_inv := by funext i; exact GrpObj.left_inv (H i).X
  right_inv := by funext i; exact GrpObj.right_inv (H i).X

/-- The group object consisting of the original family. -/
def familyGroup : Grp (∀ i, Over (Z i)) :=
  { X := fun i => (H i).X, grp := familyGrpObj H }

/-- The underlying family is in the essential image of restriction. -/
theorem family_essImage :
    (DisjointComponents.restriction p).essImage (familyGroup H).X :=
  ⟨underlying p H, ⟨Pi.isoMk fun i => componentUnderlyingIso p H i⟩⟩

/-- The family of group objects is in the essential image of restriction. -/
theorem familyGroup_essImage :
    (DisjointComponents.restriction p).mapGrp.essImage (familyGroup H) := by
  let : (DisjointComponents.restriction p).Full :=
    (DisjointComponents.restrictionFullyFaithful p).full
  let : (DisjointComponents.restriction p).Faithful :=
    (DisjointComponents.restrictionFullyFaithful p).faithful
  exact (Functor.essImage_mapGrp (F := DisjointComponents.restriction p)).mpr
    (family_essImage p H)

/-- A group scheme glued from the family, with its actual disjoint underlying scheme and a
comparison to every relative component. -/
def group : GroupScheme S :=
  Classical.choose (familyGroup_essImage p H)

/-- Its restriction is the original family as a group object. -/
def familyIso :
    (DisjointComponents.restriction p).mapGrp.obj (group p H) ≅ familyGroup H :=
  Classical.choice (Classical.choose_spec (familyGroup_essImage p H))

/-- The actual restriction of the glued group is the original group on each component,
including its multiplication. -/
def componentIso (i : I) : (baseChange (p i)).obj (group p H) ≅ H i :=
  Grp.mkIso (Pi.isoApp ((Grp.forget _).mapIso (familyIso p H)) i)
    (by
      exact congrFun (IsMonHom.one_hom (familyIso p H).hom.hom.hom) i)
    (by
      exact congrFun (IsMonHom.mul_hom (familyIso p H).hom.hom.hom) i)

/-- The glued group's underlying scheme is the actual disjoint union. -/
def underlyingIso : (group p H).X ≅ underlying p H :=
  (DisjointComponents.restrictionFullyFaithful p).preimageIso
    (((Grp.forget _).mapIso (familyIso p H)) ≪≫
      (Pi.isoMk fun i => componentUnderlyingIso p H i).symm)

/-- The structure map of the glued group is the structure map of the disjoint union, up to
the comparison `underlyingIso`. -/
theorem group_X_hom :
    (group p H).X.hom = (underlyingIso p H).hom.left ≫ (underlying p H).hom :=
  (Over.w (underlyingIso p H).hom).symm

instance [∀ i, IsAffineHom (H i).X.hom] : IsAffineHom (group p H).X.hom := by
  have h₁ : IsAffineHom (Limits.Sigma.map fun i => (H i).X.hom) :=
    P2MW.S_AlgebraicGeometry_IsZariskiLocalAtTarget_sigmaMap.solution @IsAffineHom
      (fun i => (H i).X.hom) fun i => inferInstance
  have h₂ : IsAffineHom (underlying p H).hom := by
    rw [underlying_hom]
    infer_instance
  rw [group_X_hom]
  infer_instance

end Langlands.GroupScheme.Descent.DisjointGroupGluing
