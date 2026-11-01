import Mathlib.CategoryTheory.Functor.Hom

/-!
# Renard A.V.1: the actual Hom bifunctors

The two Hom sets are lifted to a common universe without identifying the
independent Hom universes of the source and target categories.
-/

open CategoryTheory Opposite

namespace Langlands.Renard.AdjunctionHom

universe vA uA vB uB

variable {A : Type uA} [Category.{vA} A]
  {B : Type uB} [Category.{vB} B]

/-- Renard's `R_F`, with its actual precomposition and postcomposition maps. -/
def rightHomBifunctor (F : A ⥤ B) : A × Bᵒᵖ ⥤ Type (max vA vB) where
  obj p := ULift.{vA} (unop p.2 ⟶ F.obj p.1)
  map f := ↾fun ψ => ULift.up (f.2.unop ≫ ψ.down ≫ F.map f.1)
  map_id p := by
    ext ψ
    simp
  map_comp f g := by
    ext ψ
    simp [Category.assoc]

/-- Renard's `L_G`, whose underlying morphisms belong to `A`. -/
def leftHomBifunctor (G : B ⥤ A) : A × Bᵒᵖ ⥤ Type (max vA vB) where
  obj p := ULift.{vB} (G.obj (unop p.2) ⟶ p.1)
  map f := ↾fun ψ => ULift.up (G.map f.2.unop ≫ ψ.down ≫ f.1)
  map_id p := by
    ext ψ
    simp
  map_comp f g := by
    ext ψ
    simp [Category.assoc]

@[simp]
theorem rightHomBifunctor_obj (F : A ⥤ B) (p : A × Bᵒᵖ) :
    (rightHomBifunctor F).obj p =
      ULift.{vA} (unop p.2 ⟶ F.obj p.1) := rfl

@[simp]
theorem leftHomBifunctor_obj (G : B ⥤ A) (p : A × Bᵒᵖ) :
    (leftHomBifunctor G).obj p =
      ULift.{vB} (G.obj (unop p.2) ⟶ p.1) := rfl

@[simp]
theorem rightHomBifunctor_map_down (F : A ⥤ B) {p q : A × Bᵒᵖ}
    (f : p ⟶ q) (ψ : (rightHomBifunctor F).obj p) :
    ((rightHomBifunctor F).map f ψ).down =
      f.2.unop ≫ ψ.down ≫ F.map f.1 := rfl

@[simp]
theorem leftHomBifunctor_map_down (G : B ⥤ A) {p q : A × Bᵒᵖ}
    (f : p ⟶ q) (ψ : (leftHomBifunctor G).obj p) :
    ((leftHomBifunctor G).map f ψ).down =
      G.map f.2.unop ≫ ψ.down ≫ f.1 := rfl

/-- `F` is right adjoint to `G` in Renard's natural-Hom-isomorphism sense. -/
def HomAdjunction (G : B ⥤ A) (F : A ⥤ B) : Prop :=
  Nonempty (rightHomBifunctor F ≅ leftHomBifunctor G)

end Langlands.Renard.AdjunctionHom
