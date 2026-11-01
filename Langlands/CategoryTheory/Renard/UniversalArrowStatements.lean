import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic

/-!
# Right and left universal problems in Renard A.III.1

These closed propositions compare the source factorization definitions with
Mathlib's initial/terminal structured-arrow data and state uniqueness of a
comparison isomorphism compatible with the given arrows. No proofs are supplied.
-/

open CategoryTheory

universe vA vB uA uB

namespace Langlands.Renard.UniversalArrow

/-- The right universal factorization property is existence of initiality data. -/
def RightCharacterizationStatement : Prop :=
  ∀ (A : Type uA) [Category.{vA} A] (B : Type uB) [Category.{vB} B]
    (F : A ⥤ B) (Y : B) (X : A) (i : Y ⟶ F.obj X),
    (∀ (Z : A) (f : Y ⟶ F.obj Z),
      ∃! g : X ⟶ Z, i ≫ F.map g = f) ↔
    Nonempty (StructuredArrow.IsUniversal (StructuredArrow.mk (T := F) i))

/-- The left universal factorization property is existence of terminality data. -/
def LeftCharacterizationStatement : Prop :=
  ∀ (A : Type uA) [Category.{vA} A] (B : Type uB) [Category.{vB} B]
    (F : A ⥤ B) (Y : B) (X : A) (j : F.obj X ⟶ Y),
    (∀ (Z : A) (f : F.obj Z ⟶ Y),
      ∃! g : Z ⟶ X, F.map g ≫ j = f) ↔
    Nonempty (CostructuredArrow.IsUniversal (CostructuredArrow.mk (S := F) j))

/-- Two right solutions have a unique isomorphism compatible with their arrows. -/
def RightComparisonStatement : Prop :=
  ∀ (A : Type uA) [Category.{vA} A] (B : Type uB) [Category.{vB} B]
    (F : A ⥤ B) (Y : B) (X X' : A)
    (i : Y ⟶ F.obj X) (i' : Y ⟶ F.obj X'),
    (∀ (Z : A) (f : Y ⟶ F.obj Z),
      ∃! g : X ⟶ Z, i ≫ F.map g = f) →
    (∀ (Z : A) (f : Y ⟶ F.obj Z),
      ∃! g : X' ⟶ Z, i' ≫ F.map g = f) →
    ∃! e : X ≅ X', i ≫ F.map e.hom = i'

/-- Two left solutions have a unique isomorphism compatible with their arrows. -/
def LeftComparisonStatement : Prop :=
  ∀ (A : Type uA) [Category.{vA} A] (B : Type uB) [Category.{vB} B]
    (F : A ⥤ B) (Y : B) (X X' : A)
    (j : F.obj X ⟶ Y) (j' : F.obj X' ⟶ Y),
    (∀ (Z : A) (f : F.obj Z ⟶ Y),
      ∃! g : Z ⟶ X, F.map g ≫ j = f) →
    (∀ (Z : A) (f : F.obj Z ⟶ Y),
      ∃! g : Z ⟶ X', F.map g ≫ j' = f) →
    ∃! e : X ≅ X', F.map e.hom ≫ j' = j

/-- Closed aggregate of the two characterizations and compatible comparisons. -/
def UniversalArrowStatements : Prop :=
  RightCharacterizationStatement.{vA, vB, uA, uB} ∧
  LeftCharacterizationStatement.{vA, vB, uA, uB} ∧
  RightComparisonStatement.{vA, vB, uA, uB} ∧
  LeftComparisonStatement.{vA, vB, uA, uB}

end Langlands.Renard.UniversalArrow
