import Mathlib.CategoryTheory.Adjunction.Basic

/-!
# Renard A.V.1: representability and uniqueness of adjoints

Closed statements over actual functors, native adjunctions and representable
Hom presheaves, with independent object and morphism universes.
-/

open CategoryTheory

namespace Langlands.Renard.AdjointRepresentability

universe vA uA vB uB

/-- A right adjoint exists exactly when every indicated Hom presheaf is representable. -/
def RightAdjointRepresentabilityStatement : Prop :=
  ∀ (A : Type uA) [Category.{vA} A] (B : Type uB) [Category.{vB} B]
    (G : B ⥤ A),
    (∃ F : A ⥤ B, Nonempty (G ⊣ F)) ↔
      ∀ X : A, (G.op ⋙ yoneda.obj X).IsRepresentable

/-- Any two actual right adjoints of the same functor are naturally isomorphic. -/
def RightAdjointUniquenessStatement : Prop :=
  ∀ (A : Type uA) [Category.{vA} A] (B : Type uB) [Category.{vB} B]
    (G : B ⥤ A) (F F' : A ⥤ B)
    (_adj : G ⊣ F) (_adj' : G ⊣ F'),
    Nonempty (F ≅ F')

/-- Any two actual left adjoints of the same functor are naturally isomorphic. -/
def LeftAdjointUniquenessStatement : Prop :=
  ∀ (A : Type uA) [Category.{vA} A] (B : Type uB) [Category.{vB} B]
    (F : A ⥤ B) (G G' : B ⥤ A)
    (_adj : G ⊣ F) (_adj' : G' ⊣ F),
    Nonempty (G ≅ G')

/-- The representability criterion, right uniqueness and left uniqueness, in source order. -/
def AdjointRepresentabilityStatements : Prop :=
  RightAdjointRepresentabilityStatement.{vA, uA, vB, uB} ∧
    RightAdjointUniquenessStatement.{vA, uA, vB, uB} ∧
    LeftAdjointUniquenessStatement.{vA, uA, vB, uB}

end Langlands.Renard.AdjointRepresentability
