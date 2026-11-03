import Langlands.GroupScheme.SchemeActionRationalPoints

/-! # Orbit morphisms and translations for actions on schemes -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SchemeAction

variable {S : Scheme.{u}} {H : GroupScheme S} {X Y : Over S}
variable (a : SchemeAction H X)

/-- The orbit as a subset of the underlying scheme. -/
def orbit (x : 𝟙_ (Over S) ⟶ X) : Set X.left :=
  Set.range (a.orbitMap x).left

/-- Translation of the acted-on scheme by a section of the acting group. -/
def translation (h : 𝟙_ (Over S) ⟶ H.X) : X ⟶ X :=
  a.act (toUnit X ≫ h) (𝟙 X)

/-- Translation evaluates to the action on every test scheme. -/
@[reassoc]
theorem comp_translation {T : Over S} (f : T ⟶ X)
    (h : 𝟙_ (Over S) ⟶ H.X) :
    f ≫ a.translation h = a.act (toUnit T ≫ h) f := by
  rw [translation, a.naturality]
  simp only [comp_toUnit_assoc, Category.comp_id]

/-- Translation by the identity section is the identity morphism. -/
@[simp]
theorem translation_one : a.translation 1 = 𝟙 X := by
  rw [translation, MonObj.comp_one, a.act_one]

/-- Composition of translations is the action multiplication law. -/
theorem translation_mul (h h' : 𝟙_ (Over S) ⟶ H.X) :
    a.translation (h * h') = a.translation h' ≫ a.translation h := by
  rw [a.comp_translation, translation, MonObj.comp_mul, a.act_mul]
  rfl

/-- Every translation is an isomorphism, with inverse the inverse translation. -/
def translationIso (h : 𝟙_ (Over S) ⟶ H.X) : X ≅ X where
  hom := a.translation h
  inv := a.translation h⁻¹
  hom_inv_id := by rw [← a.translation_mul, inv_mul_cancel, a.translation_one]
  inv_hom_id := by rw [← a.translation_mul, mul_inv_cancel, a.translation_one]

/-- Equivariant scheme morphisms intertwine the actual orbit morphisms. -/
theorem orbitMap_comp (b : SchemeAction H Y) (f : X ⟶ Y)
    (hf : ∀ (T : Over S) (h : T ⟶ H.X) (x : T ⟶ X),
      a.act h x ≫ f = b.act h (x ≫ f))
    (x : 𝟙_ (Over S) ⟶ X) :
    a.orbitMap x ≫ f = b.orbitMap (x ≫ f) := by
  simpa only [orbitMap, Category.assoc] using
    hf H.X (𝟙 H.X) (toUnit H.X ≫ x)

/-- Equivariant maps carry the underlying orbit onto the corresponding orbit. -/
theorem image_orbit (b : SchemeAction H Y) (f : X ⟶ Y)
    (hf : ∀ (T : Over S) (h : T ⟶ H.X) (x : T ⟶ X),
      a.act h x ≫ f = b.act h (x ≫ f))
    (x : 𝟙_ (Over S) ⟶ X) :
    f.left '' a.orbit x = b.orbit (x ≫ f) := by
  rw [orbit, orbit, ← Set.range_comp]
  apply congrArg Set.range
  funext z
  simpa only [Over.comp_left, Scheme.Hom.comp_apply, Function.comp_apply] using
    congrArg (fun q : H.X ⟶ Y => q.left z) (a.orbitMap_comp b f hf x)

end Langlands.GroupScheme.SchemeAction
