import Mathlib.CategoryTheory.Yoneda
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.Equivalence

/-!
# Renard A.III.2: Yoneda and representable presheaves

Statement-only formulations over the actual Mathlib Yoneda embedding,
representations and full subcategory. Independent value and morphism universes
are compared by explicit universe lifts.
-/

universe w v u

open CategoryTheory Opposite

namespace Langlands.Renard.Yoneda

/-- Evaluation at the identity and its explicit inverse, with independent universes. -/
def EvaluationStatement : Prop :=
  ∀ (C : Type u) [Category.{v} C] (F : Cᵒᵖ ⥤ Type w) (X : C),
    ∃ e : (uliftYoneda.{w}.obj X ⟶ F ⋙ uliftFunctor.{v}) ≃ F.obj (op X),
      (∀ θ, e θ = (θ.app (op X) (ULift.up (𝟙 X))).down) ∧
      (∀ (x : F.obj (op X)) (Y : C) (f : Y ⟶ X),
        (e.symm x).app (op Y) (ULift.up f) = ULift.up (F.map f.op x))

/-- The actual lifted Yoneda map gives a Hom equivalence, with explicit inverse. -/
def HomEquivalenceStatement : Prop :=
  ∀ (C : Type u) [Category.{v} C] (X Y : C),
    ∃ e : (X ⟶ Y) ≃ (uliftYoneda.{w}.obj X ⟶ uliftYoneda.{w}.obj Y),
      (∀ f, e f = uliftYoneda.{w}.map f) ∧
      (∀ θ, e.symm θ = (θ.app (op X) (ULift.up (𝟙 X))).down)

/-- Natural Hom equivalences agree with the source's natural-isomorphism definition. -/
def RepresentationDictionaryStatement : Prop :=
  ∀ (C : Type u) [Category.{v} C] (F : Cᵒᵖ ⥤ Type w) (X : C),
    Nonempty (F.RepresentableBy X) ↔
      Nonempty (uliftYoneda.{w}.obj X ≅ F ⋙ uliftFunctor.{v})

/-- The full-subcategory equivalence is induced by the actual Yoneda embedding. -/
def RepresentableEquivalenceStatement : Prop :=
  ∀ (C : Type u) [Category.{v} C],
    let P : ObjectProperty (Cᵒᵖ ⥤ Type (max w v)) := fun F => F.IsRepresentable
    ∃ e : C ≌ P.FullSubcategory,
      Nonempty (e.functor ⋙ P.ι ≅ uliftYoneda.{w} (C := C))

/-- The four closed propositions, in evaluation, Hom, dictionary, equivalence order. -/
def YonedaStatements : Prop :=
  EvaluationStatement.{w, v, u} ∧
    HomEquivalenceStatement.{w, v, u} ∧
    RepresentationDictionaryStatement.{w, v, u} ∧
    RepresentableEquivalenceStatement.{w, v, u}

end Langlands.Renard.Yoneda
