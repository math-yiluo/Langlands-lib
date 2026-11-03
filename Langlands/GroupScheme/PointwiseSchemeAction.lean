import Langlands.GroupScheme.AffineCorepresented
import Langlands.GroupScheme.AutomorphicAction

/-! # Group-scheme actions specified by laws on all test points -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false

namespace Langlands.GroupScheme

variable {S : Scheme.{u}}

/-- An actual group-scheme action on a scheme over the base. -/
structure PointwiseSchemeAction (H : GroupScheme S) (X : Over S) where
  hom : H.X ⊗ X ⟶ X
  one_left : ∀ {T : Over S} (x : T ⟶ X), lift (1 : T ⟶ H.X) x ≫ hom = x
  mul_left : ∀ {T : Over S} (h h' : T ⟶ H.X) (x : T ⟶ X),
    lift (h * h') x ≫ hom = lift h (lift h' x ≫ hom) ≫ hom

namespace PointwiseSchemeAction

variable {H : GroupScheme S} {X : Over S} (a : PointwiseSchemeAction H X)

/-- The point action induced by the action morphism. -/
def act {T : Over S} (h : T ⟶ H.X) (x : T ⟶ X) : T ⟶ X :=
  lift h x ≫ a.hom

@[simp] theorem act_one_left {T : Over S} (x : T ⟶ X) : a.act 1 x = x :=
  a.one_left x

theorem act_mul_left {T : Over S} (h h' : T ⟶ H.X) (x : T ⟶ X) :
    a.act (h * h') x = a.act h (a.act h' x) :=
  a.mul_left h h' x

/-- The action is natural for every morphism of test schemes. -/
theorem naturality {T T' : Over S} (b : T' ⟶ T) (h : T ⟶ H.X) (x : T ⟶ X) :
    b ≫ a.act h x = a.act (b ≫ h) (b ≫ x) := by
  unfold act
  rw [← Category.assoc, comp_lift]

/-- Fixedness is imposed after every scheme refinement. -/
def IsFixed {T : Over S} (x : T ⟶ X) : Prop :=
  ∀ (T' : Over S) (b : T' ⟶ T) (h : T' ⟶ H.X), a.act h (b ≫ x) = b ≫ x

/-- The universal acting point tests all-refinement fixedness. -/
theorem isFixed_iff_universal {T : Over S} (x : T ⟶ X) :
    a.IsFixed x ↔
      a.act (snd T H.X) (fst T H.X ≫ x) = fst T H.X ≫ x := by
  constructor
  · intro hx
    exact hx _ (fst T H.X) (snd T H.X)
  · intro hx T' b h
    have e := congrArg (fun f => lift b h ≫ f) hx
    simpa only [naturality, lift_snd, lift_fst_assoc] using e

/-- For an affine acting group and an affine test, algebra refinements suffice. -/
theorem isFixed_iff_affineRefinements {R : CommRingCat.{u}}
    {H : GroupScheme (Spec R)} {X : Over (Spec R)}
    [IsAffine H.X.left] (a : PointwiseSchemeAction H X) {C : CommAlgCat.{u} R}
    (x : (algSpec R).obj (op C) ⟶ X) :
    a.IsFixed x ↔
      ∀ (D : CommAlgCat.{u} R) (f : C ⟶ D)
        (h : (algSpec R).obj (op D) ⟶ H.X),
        a.act h ((algSpec R).map f.op ≫ x) = (algSpec R).map f.op ≫ x := by
  constructor
  · intro hx D f h
    exact hx _ ((algSpec R).map f.op) h
  · intro hx
    rw [a.isFixed_iff_universal]
    let T := (algSpec R).obj (op C)
    let : IsAffine T.left := by
      change IsAffine (Spec (CommRingCat.of C))
      infer_instance
    have : IsAffine (T ⊗ H.X).left := by
      change IsAffine (CategoryTheory.Limits.pullback T.hom H.X.hom)
      infer_instance
    have hW : (algSpec R).essImage (T ⊗ H.X) := essImage_algSpec.mpr (by infer_instance)
    let D := hW.witness.unop
    let e : (algSpec R).obj (op D) ≅ T ⊗ H.X := hW.getIso
    let f : C ⟶ D := (algSpec.fullyFaithful.preimage (e.hom ≫ fst T H.X)).unop
    have he : (algSpec R).map f.op = e.hom ≫ fst T H.X :=
      algSpec.fullyFaithful.map_preimage _
    have h := hx D f (e.hom ≫ snd T H.X)
    rw [he, Category.assoc] at h
    apply (cancel_epi e.hom).1
    rw [a.naturality, ← Category.assoc]
    exact h

end PointwiseSchemeAction

namespace AutomorphicAction

variable {H G : GroupScheme S} (a : AutomorphicAction H G)

/-- Forget preservation of the target group law. -/
def toPointwiseSchemeAction : PointwiseSchemeAction H G.X where
  hom := a.hom
  one_left := a.one_left
  mul_left := a.mul_left

@[simp] theorem toPointwiseSchemeAction_act {T : Over S} (h : T ⟶ H.X) (g : T ⟶ G.X) :
    a.toPointwiseSchemeAction.act h g = a.act h g := rfl

end AutomorphicAction

end Langlands.GroupScheme
