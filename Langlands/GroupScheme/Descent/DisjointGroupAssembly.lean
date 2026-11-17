import Langlands.GroupScheme.Descent.DisjointComponentHoms

/-! # Assembling group schemes over a finite disjoint decomposition -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.Descent.DisjointGroupAssembly

variable {I : Type u} [Finite I] {S : Scheme.{u}} {Z : I → Scheme.{u}}
  (p : ∀ i, Z i ⟶ S) [IsIso (Sigma.desc p)] (H : ∀ i, GroupScheme (Z i))

attribute [local instance] DisjointComponents.pointwiseCartesianMonoidalCategory

/-- The disjoint union of the underlying schemes, over the decomposed base. -/
def underlying : Over S :=
  Over.mk (Sigma.desc fun i => (H i).X.hom ≫ p i)

/-- A component of the assembled underlying scheme is a genuine pullback. -/
theorem component_isPullback (i : I) :
    IsPullback (Sigma.ι (fun j => (H j).X.left) i) (H i).X.hom
      (underlying p H).hom (p i) := by
  have hc : IsColimit (Cofan.mk S p) :=
    ((Cofan.nonempty_isColimit_iff_isIso_sigmaDesc _).mpr
      (inferInstanceAs (IsIso (Sigma.desc p)))).some
  have hVK := FinitaryExtensive.isVanKampen_finiteCoproducts hc
  exact (hVK (Cofan.mk _ (Sigma.ι (fun j => (H j).X.left)))
    (Discrete.natTrans fun j => (H j.as).X.hom) (underlying p H).hom
    (by ext ⟨j⟩; simp [underlying])
    (.of_discrete _)).mp ⟨coproductIsCoproduct _⟩ ⟨i⟩

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

/-- A group scheme assembled from the family, with its actual disjoint
underlying scheme and a comparison to every relative component. -/
def group : GroupScheme S :=
  Classical.choose (familyGroup_essImage p H)

/-- Its restriction is the original family as a group object. -/
def familyIso :
    (DisjointComponents.restriction p).mapGrp.obj (group p H) ≅ familyGroup H :=
  Classical.choice (Classical.choose_spec (familyGroup_essImage p H))

/-- The actual restriction of the assembled group is the original group on
each component, including its multiplication. -/
def componentIso (i : I) : (baseChange (p i)).obj (group p H) ≅ H i :=
  Grp.mkIso (Pi.isoApp ((Grp.forget _).mapIso (familyIso p H)) i)
    (by
      exact congrFun (IsMonHom.one_hom (familyIso p H).hom.hom.hom) i)
    (by
      exact congrFun (IsMonHom.mul_hom (familyIso p H).hom.hom.hom) i)

/-- The assembled group's underlying scheme is the actual disjoint union. -/
def underlyingIso : (group p H).X ≅ underlying p H :=
  (DisjointComponents.restrictionFullyFaithful p).preimageIso
    (((Grp.forget _).mapIso (familyIso p H)) ≪≫
      (Pi.isoMk fun i => componentUnderlyingIso p H i).symm)

instance [∀ i, IsAffine (H i).X.left] : IsAffine (group p H).X.left := by
  let : IsAffine (underlying p H).left :=
    inferInstanceAs (IsAffine (∐ fun i => (H i).X.left))
  exact IsAffine.of_isIso (underlyingIso p H).hom.left

end Langlands.GroupScheme.Descent.DisjointGroupAssembly
