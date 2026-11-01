import Mathlib.CategoryTheory.Yoneda

/-!
# Renard A.III.3: the object and functor isomorphism principles

These closed propositions spell out the naturality of the source Hom-set
equivalences and conclude existence of actual categorical isomorphisms.
They do not supply proofs of either principle.
-/

open CategoryTheory

universe vC vM uC uM

namespace Langlands.Renard.IsomorphismPrinciple

/-- Natural equivalences of represented Hom sets imply an object isomorphism. -/
def ObjectStatement : Prop :=
  ∀ (M : Type uM) [Category.{vM} M] (X Y : M)
    (e : ∀ Z : M, (Z ⟶ X) ≃ (Z ⟶ Y)),
    (∀ (Z Z' : M) (g : Z' ⟶ Z) (f : Z ⟶ X),
      e Z' (g ≫ f) = g ≫ e Z f) →
    Nonempty (X ≅ Y)

/-- Hom equivalences natural in both variables imply a natural isomorphism. -/
def FunctorStatement : Prop :=
  ∀ (C : Type uC) [Category.{vC} C] (M : Type uM) [Category.{vM} M]
    (F G : C ⥤ M)
    (e : ∀ (X : C) (Z : M), (Z ⟶ F.obj X) ≃ (Z ⟶ G.obj X)),
    (∀ (X : C) (Z Z' : M) (g : Z' ⟶ Z) (f : Z ⟶ F.obj X),
      e X Z' (g ≫ f) = g ≫ e X Z f) →
    (∀ (X X' : C) (a : X ⟶ X') (Z : M) (f : Z ⟶ F.obj X),
      e X' Z (f ≫ F.map a) = e X Z f ≫ G.map a) →
    Nonempty (F ≅ G)

/-- Closed aggregate of the object and functor principles, in source order. -/
def IsomorphismPrincipleStatements : Prop :=
  ObjectStatement.{vM, uM} ∧ FunctorStatement.{vC, vM, uC, uM}

end Langlands.Renard.IsomorphismPrinciple
