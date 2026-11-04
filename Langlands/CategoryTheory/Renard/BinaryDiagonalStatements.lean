import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
import Mathlib.CategoryTheory.Products.Basic
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.BinaryFan

/-!
# Renard A.III.1: binary products and coproducts through the diagonal

These closed propositions identify the universal arrows for the actual diagonal
functor with the two-map factorization properties and with the corresponding
binary limit and colimit witnesses. This file supplies statements only.
-/

open CategoryTheory CategoryTheory.Limits

universe vC uC

namespace Langlands.Renard.BinaryDiagonal

/-- A left universal arrow for the diagonal has the binary product factorization property. -/
def ProductFactorizationStatement : Prop :=
  ∀ (C : Type uC) [Category.{vC} C] (X Y P : C)
    (p : P ⟶ X) (q : P ⟶ Y),
    Nonempty (CostructuredArrow.IsUniversal
      (CostructuredArrow.mk (S := Functor.diag C) (CategoryTheory.Prod.mkHom p q))) ↔
    ∀ (Z : C) (f : Z ⟶ X) (g : Z ⟶ Y),
      ∃! l : Z ⟶ P, l ≫ p = f ∧ l ≫ q = g

/-- A left universal diagonal arrow is exactly a limiting binary fan on its projections. -/
def ProductLimitStatement : Prop :=
  ∀ (C : Type uC) [Category.{vC} C] (X Y P : C)
    (p : P ⟶ X) (q : P ⟶ Y),
    Nonempty (CostructuredArrow.IsUniversal
      (CostructuredArrow.mk (S := Functor.diag C) (CategoryTheory.Prod.mkHom p q))) ↔
    Nonempty (IsLimit (BinaryFan.mk p q))

/-- A right universal arrow for the diagonal has the binary coproduct factorization property. -/
def CoproductFactorizationStatement : Prop :=
  ∀ (C : Type uC) [Category.{vC} C] (X Y Q : C)
    (i : X ⟶ Q) (j : Y ⟶ Q),
    Nonempty (StructuredArrow.IsUniversal
      (StructuredArrow.mk (T := Functor.diag C) (CategoryTheory.Prod.mkHom i j))) ↔
    ∀ (Z : C) (f : X ⟶ Z) (g : Y ⟶ Z),
      ∃! l : Q ⟶ Z, i ≫ l = f ∧ j ≫ l = g

/-- A right universal diagonal arrow is exactly a colimiting binary cofan on its inclusions. -/
def CoproductColimitStatement : Prop :=
  ∀ (C : Type uC) [Category.{vC} C] (X Y Q : C)
    (i : X ⟶ Q) (j : Y ⟶ Q),
    Nonempty (StructuredArrow.IsUniversal
      (StructuredArrow.mk (T := Functor.diag C) (CategoryTheory.Prod.mkHom i j))) ↔
    Nonempty (IsColimit (BinaryCofan.mk i j))

/-- The two diagonal factorization characterizations and their binary (co)limit comparisons. -/
def BinaryDiagonalStatements : Prop :=
  ProductFactorizationStatement.{vC, uC} ∧
  ProductLimitStatement.{vC, uC} ∧
  CoproductFactorizationStatement.{vC, uC} ∧
  CoproductColimitStatement.{vC, uC}

end Langlands.Renard.BinaryDiagonal
