import Langlands.GroupScheme.SchemeAction

/-! # Translation by a rational point of the acting group -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SchemeActionTranslation

open SchemeAction

variable {S : Scheme.{u}} {H : GroupScheme S} {X : Over S} (a : SchemeAction H X)

/-- Translation `x ↦ h • x` of `X` by a section `h` of the acting group over the base. -/
def translate (h : Over.mk (𝟙 S) ⟶ H.X) : X ⟶ X :=
  a.act (toUnit X ≫ h) (𝟙 X)

/-- On points, translation is the action of the constant point `h`. -/
theorem comp_translate (h : Over.mk (𝟙 S) ⟶ H.X) {W : Over S} (w : W ⟶ X) :
    w ≫ translate a h = a.act (toUnit W ≫ h) w := by
  rw [translate, naturality, comp_toUnit_assoc, Category.comp_id]

theorem translate_comp (h h' : Over.mk (𝟙 S) ⟶ H.X) :
    translate a h ≫ translate a h' = translate a (h' * h) := by
  rw [comp_translate, translate, ← act_mul, ← MonObj.comp_mul]
  rfl

theorem translate_one : translate a 1 = 𝟙 X := by
  rw [translate, MonObj.comp_one, act_one]

instance (h : Over.mk (𝟙 S) ⟶ H.X) : IsIso (translate a h) :=
  ⟨⟨translate a h⁻¹, by rw [translate_comp, inv_mul_cancel, translate_one],
    by rw [translate_comp, mul_inv_cancel, translate_one]⟩⟩

instance (h : Over.mk (𝟙 S) ⟶ H.X) : IsIso (translate a h).left :=
  (inferInstance : IsIso ((Over.forget S).map (translate a h)))

/-- Translation preserves specialization chains of scheme points with distinct members, and
closed points. -/
theorem chain_translate (h : Over.mk (𝟙 S) ⟶ H.X) {y₀ y₁ z : X.left} (h₀₁ : y₀ ⤳ y₁)
    (h₁z : y₁ ⤳ z) (hne₀₁ : y₀ ≠ y₁) (hne₁z : y₁ ≠ z) :
    (translate a h).left y₀ ⤳ (translate a h).left y₁ ∧
      (translate a h).left y₁ ⤳ (translate a h).left z ∧
      (translate a h).left y₀ ≠ (translate a h).left y₁ ∧
      (translate a h).left y₁ ≠ (translate a h).left z := by
  have hinj : Function.Injective (translate a h).left := (translate a h).left.homeomorph.injective
  exact ⟨h₀₁.map (translate a h).left.continuous, h₁z.map (translate a h).left.continuous,
    hinj.ne hne₀₁, hinj.ne hne₁z⟩

theorem isClosed_translate (h : Over.mk (𝟙 S) ⟶ H.X) {z : X.left}
    (hz : IsClosed ({z} : Set X.left)) :
    IsClosed ({(translate a h).left z} : Set X.left) := by
  have := (translate a h).left.homeomorph.isClosedMap _ hz
  rwa [Set.image_singleton] at this

end Langlands.GroupScheme.SchemeActionTranslation
