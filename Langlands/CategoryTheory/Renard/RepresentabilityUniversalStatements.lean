import Mathlib.CategoryTheory.Yoneda
import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic

/-!
# Renard A.III.2: representability and left universal problems

Closed statement-only formulations of the final remark and corollary.
The comparison of universe levels uses the actual lifted Yoneda embedding.
-/

universe w vA vB uA uB

open CategoryTheory Opposite

namespace Langlands.Renard.RepresentabilityUniversal

/-- A chosen transformation represents a presheaf exactly when it is universal. -/
def YonedaUniversalStatement : Prop :=
  ∀ (C : Type uA) [Category.{vA} C] (F : Cᵒᵖ ⥤ Type w) (X : C)
    (ω : uliftYoneda.{w}.obj X ⟶ F ⋙ uliftFunctor.{vA}),
    IsIso ω ↔
      Nonempty (CostructuredArrow.IsUniversal
        (CostructuredArrow.mk (S := uliftYoneda.{w} (C := C)) ω))

/-- A represented Hom presheaf gives the original left universal arrow. -/
def HomPresheafUniversalStatement : Prop :=
  ∀ (A : Type uA) [Category.{vA} A] (B : Type uB) [Category.{vB} B]
    (F : A ⥤ B) (Y : B) (X : A)
    (r : (F.op ⋙ yoneda.obj Y).RepresentableBy X),
    Nonempty (CostructuredArrow.IsUniversal
      (CostructuredArrow.mk (S := F) (r.homEquiv (𝟙 X))))

/-- The comparison of representing objects is unique with its compatibility law. -/
def CompatibleUniquenessStatement : Prop :=
  ∀ (C : Type uA) [Category.{vA} C] (F : Cᵒᵖ ⥤ Type w) (X X' : C)
    (ω : uliftYoneda.{w}.obj X ≅ F ⋙ uliftFunctor.{vA})
    (ω' : uliftYoneda.{w}.obj X' ≅ F ⋙ uliftFunctor.{vA}),
    ∃! e : X ≅ X', uliftYoneda.{w}.map e.hom ≫ ω'.hom = ω.hom

/-- The two universal-property assertions and compatible uniqueness, in source order. -/
def RepresentabilityUniversalStatements : Prop :=
  YonedaUniversalStatement.{w, vA, uA} ∧
    HomPresheafUniversalStatement.{vA, vB, uA, uB} ∧
    CompatibleUniquenessStatement.{w, vA, uA}

end Langlands.Renard.RepresentabilityUniversal
