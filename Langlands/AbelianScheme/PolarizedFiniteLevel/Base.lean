import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-! # The full category of bases for ordinary finite-level moduli -/

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

/-- The only conditions on an actual universe-zero base are local
noetherianity and invertibility of the level in its global sections. -/
def levelBaseProperty (n : ℕ) (S : Scheme.{0}) : Prop :=
  IsLocallyNoetherian S ∧ IsUnit (n : Γ(S, ⊤))

/-- The full category of locally noetherian actual schemes where `n` is
invertible, with every actual scheme morphism between its objects. -/
abbrev LevelBase (n : ℕ) : Type 1 :=
  ObjectProperty.FullSubcategory (levelBaseProperty n)

namespace LevelBase

variable {n : ℕ}

instance locallyNoetherian (S : LevelBase n) : IsLocallyNoetherian S.obj :=
  S.property.1

/-- The level is a unit on every object of the base category. -/
theorem level_isUnit (S : LevelBase n) : IsUnit (n : Γ(S.obj, ⊤)) :=
  S.property.2

/-- Include an actual scheme with the two required properties. -/
def ofScheme (S : Scheme.{0}) [IsLocallyNoetherian S]
    (hn : IsUnit (n : Γ(S, ⊤))) : LevelBase n :=
  ⟨S, inferInstance, hn⟩

/-- The fully faithful forgetful functor to actual universe-zero schemes. -/
abbrev forget (n : ℕ) : LevelBase n ⥤ Scheme.{0} :=
  ObjectProperty.ι (levelBaseProperty n)

/-- Every actual scheme morphism between these objects is a morphism in
the base category; no condition on the morphism is required. -/
abbrev homMk {S T : LevelBase n} (b : S.obj ⟶ T.obj) : S ⟶ T :=
  ObjectProperty.homMk b

/-- The hom types are equivalent to all actual scheme morphisms. -/
def homEquiv (S T : LevelBase n) : (S ⟶ T) ≃ (S.obj ⟶ T.obj) where
  toFun b := b.hom
  invFun b := homMk b
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
theorem forget_obj (S : LevelBase n) : (forget n).obj S = S.obj :=
  rfl

@[simp]
theorem forget_map {S T : LevelBase n} (b : S ⟶ T) :
    (forget n).map b = b.hom :=
  rfl

@[simp]
theorem forget_map_homMk {S T : LevelBase n} (b : S.obj ⟶ T.obj) :
    (forget n).map (homMk b) = b :=
  rfl

end LevelBase

end Langlands.AbelianScheme.PolarizedFiniteLevel
