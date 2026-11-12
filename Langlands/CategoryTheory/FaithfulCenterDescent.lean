import Mathlib.CategoryTheory.Center.Preadditive
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-! # Descent of the categorical center along a faithful additive functor -/

noncomputable section

universe vC vD uC uD

open CategoryTheory

namespace Langlands.Renard

variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
  [Preadditive C] [Preadditive D]

/-- Every component of a target central transformation on the image of `I` lifts
through `I`. Naturality and the ring laws are consequences of faithfulness. -/
def CenterComponentsLift (I : C ⥤ D) : Prop :=
  ∀ (z : CatCenter D) (X : C), ∃ f : X ⟶ X, I.map f = z.app (I.obj X)

variable (I : C ⥤ D) [I.Faithful] [I.Additive] (h : CenterComponentsLift I)

private def centerLiftComponent (z : CatCenter D) (X : C) : X ⟶ X :=
  (h z X).choose

omit [Preadditive C] [Preadditive D] [I.Faithful] [I.Additive] in
private theorem map_centerLiftComponent (z : CatCenter D) (X : C) :
    I.map (centerLiftComponent I h z X) = z.app (I.obj X) :=
  (h z X).choose_spec

private def centerLift (z : CatCenter D) : CatCenter C where
  app := centerLiftComponent I h z
  naturality := fun X Y f => by
    change f ≫ centerLiftComponent I h z Y = centerLiftComponent I h z X ≫ f
    apply I.map_injective
    simp only [Functor.map_comp, map_centerLiftComponent]
    exact CatCenter.naturality z (I.map f)

omit [Preadditive C] [Preadditive D] [I.Additive] in
private theorem map_centerLift (z : CatCenter D) (X : C) :
    I.map ((centerLift I h z).app X) = z.app (I.obj X) :=
  map_centerLiftComponent I h z X

/-- The unique ring homomorphism descending the target center along a faithful
additive functor, when its central components lift pointwise. -/
def faithfulCenterDescent : CatCenter D →+* CatCenter C where
  toFun := centerLift I h
  map_one' := by
    apply CatCenter.ext
    intro X
    apply I.map_injective
    rw [map_centerLift]
    exact (I.map_id X).symm
  map_mul' z w := by
    apply CatCenter.ext
    intro X
    apply I.map_injective
    change I.map ((centerLift I h (z * w)).app X) =
      I.map ((centerLift I h w).app X ≫ (centerLift I h z).app X)
    rw [map_centerLift, I.map_comp, map_centerLift, map_centerLift]
    rfl
  map_zero' := by
    apply CatCenter.ext
    intro X
    apply I.map_injective
    rw [map_centerLift]
    exact (I.map_zero X X).symm
  map_add' z w := by
    apply CatCenter.ext
    intro X
    apply I.map_injective
    change I.map ((centerLift I h (z + w)).app X) =
      I.map ((centerLift I h z).app X + (centerLift I h w).app X)
    rw [map_centerLift, I.map_add, map_centerLift, map_centerLift]
    rfl

@[simp]
theorem faithfulCenterDescent_map_app (z : CatCenter D) (X : C) :
    I.map ((faithfulCenterDescent I h z).app X) = z.app (I.obj X) :=
  map_centerLift I h z X

/-- Compatibility with a faithful functor determines the descended center map. -/
theorem faithfulCenterDescent_unique (φ : CatCenter D →+* CatCenter C)
    (hφ : ∀ (z : CatCenter D) (X : C), I.map ((φ z).app X) = z.app (I.obj X)) :
    φ = faithfulCenterDescent I h := by
  apply RingHom.ext
  intro z
  apply CatCenter.ext
  intro X
  apply I.map_injective
  rw [hφ, faithfulCenterDescent_map_app]

omit [Preadditive C] [Preadditive D] [I.Faithful] [I.Additive] in
/-- A compatibility on a right adjoint transfers to its left adjoint. For normalized
parabolic functors this is the Jacquet compatibility from the induction compatibility,
using Frobenius reciprocity. -/
theorem center_compatibility_leftAdjoint {R : D ⥤ C} (adj : R ⊣ I)
    (z : CatCenter D) (w : CatCenter C)
    (hI : ∀ X : C, I.map (w.app X) = z.app (I.obj X)) (Y : D) :
    R.map (z.app Y) = w.app (R.obj Y) := by
  apply (adj.homEquiv Y (R.obj Y)).injective
  calc
    adj.homEquiv Y (R.obj Y) (R.map (z.app Y)) =
        z.app Y ≫ adj.unit.app Y := by
      simpa only [Category.comp_id, adj.homEquiv_id] using adj.homEquiv_naturality_left (z.app Y) (𝟙 (R.obj Y))
    _ = adj.unit.app Y ≫ z.app (I.obj (R.obj Y)) :=
      (CatCenter.naturality z (adj.unit.app Y)).symm
    _ = adj.unit.app Y ≫ I.map (w.app (R.obj Y)) := by rw [hI]
    _ = adj.homEquiv Y (R.obj Y) (w.app (R.obj Y)) := rfl

/-- The descended center action is compatible with every specified left adjoint. -/
theorem faithfulCenterDescent_leftAdjoint {R : D ⥤ C} (adj : R ⊣ I)
    (z : CatCenter D) (Y : D) :
    R.map (z.app Y) = (faithfulCenterDescent I h z).app (R.obj Y) :=
  center_compatibility_leftAdjoint I adj z (faithfulCenterDescent I h z)
    (faithfulCenterDescent_map_app I h z) Y

end Langlands.Renard
