import Langlands.AbelianScheme.GroupScheme
import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod

/-! # Group-scheme actions on schemes and all-test fixed points -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {S : Scheme.{u}}

/-- An action of a group scheme on a scheme over the same base: the existing
categorical module-object structure, with its actual action morphism. -/
abbrev SchemeAction (H : GroupScheme S) (X : Over S) := ModObj H.X X

namespace SchemeAction

variable {H K : GroupScheme S} {X : Over S} (a : SchemeAction H X)

/-- The scheme morphism defining the action. -/
def hom : H.X ⊗ X ⟶ X :=
  letI := a
  γ[H.X, X]

/-- The action on points of every test scheme. -/
def act {T : Over S} (h : T ⟶ H.X) (x : T ⟶ X) : T ⟶ X :=
  lift h x ≫ a.hom

@[simp] theorem act_one {T : Over S} (x : T ⟶ X) : a.act 1 x = x := by
  let : ModObj H.X X := a
  exact one_smul (T ⟶ H.X) x

theorem act_mul {T : Over S} (h h' : T ⟶ H.X) (x : T ⟶ X) :
    a.act (h * h') x = a.act h (a.act h' x) := by
  let : ModObj H.X X := a
  exact mul_smul h h' x

theorem naturality {T T' : Over S} (b : T' ⟶ T) (h : T ⟶ H.X) (x : T ⟶ X) :
    b ≫ a.act h x = a.act (b ≫ h) (b ≫ x) := by
  unfold act
  rw [← Category.assoc, comp_lift]

/-- Restrict an action along an actual group-scheme homomorphism. -/
@[instance_reducible] def restrict (f : K ⟶ H) : SchemeAction K X :=
  letI := a
  Mod.scalarRestriction f.hom.hom X

@[simp] theorem restrict_act (f : K ⟶ H) {T : Over S}
    (h : T ⟶ K.X) (x : T ⟶ X) :
    (a.restrict f).act h x = a.act (h ≫ f.hom.hom) x := by
  change lift h x ≫ ((f.hom.hom ▷ X) ≫ a.hom) =
    lift (h ≫ f.hom.hom) x ≫ a.hom
  rw [lift_whiskerRight_assoc]

/-- A point is fixed after every change of test scheme. -/
def IsFixed {T : Over S} (x : T ⟶ X) : Prop :=
  ∀ (T' : Over S) (b : T' ⟶ T) (h : T' ⟶ H.X), a.act h (b ≫ x) = b ≫ x

/-- All-test fixedness is equivalent to its universal product equation. -/
theorem isFixed_iff_universal {T : Over S} (x : T ⟶ X) :
    a.IsFixed x ↔
      a.act (snd T H.X) (fst T H.X ≫ x) = fst T H.X ≫ x := by
  constructor
  · intro hx
    exact hx _ (fst T H.X) (snd T H.X)
  · intro hx T' b h
    have e := congrArg (fun f => lift b h ≫ f) hx
    simpa only [naturality, lift_snd, lift_fst_assoc] using e

/-- Fixedness is stable under every further test morphism. -/
theorem IsFixed.comp {T T' : Over S} {x : T ⟶ X}
    (hx : a.IsFixed x) (b : T' ⟶ T) : a.IsFixed (b ≫ x) := by
  intro T'' c h
  simpa only [Category.assoc] using hx T'' (c ≫ b) h

/-- Restricting the acting group preserves fixed points. -/
theorem IsFixed.restrict {T : Over S} {x : T ⟶ X}
    (hx : a.IsFixed x) (f : K ⟶ H) : (a.restrict f).IsFixed x := by
  intro T' b h
  rw [restrict_act]
  exact hx T' b (h ≫ f.hom.hom)

end SchemeAction

end Langlands.GroupScheme
