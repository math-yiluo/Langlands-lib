import Mathlib.CategoryTheory.Adjunction.Basic

/-!
# Renard A.V.2: unit, counit and the two Hom maps

Statements over actual Mathlib adjunctions and arbitrary actual natural
transformations, with four independent category universes.
-/

open CategoryTheory

namespace Langlands.Renard.UnitCounit

universe vA uA vB uB

/-- The unit and counit are the images of the appropriate identity arrows. -/
def UnitCounitAtIdentitiesStatement : Prop :=
  ∀ (A : Type uA) [Category.{vA} A] (B : Type uB) [Category.{vB} B]
    (G : B ⥤ A) (F : A ⥤ B) (adj : G ⊣ F),
    (∀ Y : B, adj.unit.app Y =
      adj.homEquiv Y (G.obj Y) (𝟙 (G.obj Y))) ∧
    (∀ X : A, adj.counit.app X =
      (adj.homEquiv (F.obj X) X).symm (𝟙 (F.obj X)))

/-- Component naturality for the actual unit and counit. -/
def UnitCounitNaturalityStatement : Prop :=
  ∀ (A : Type uA) [Category.{vA} A] (B : Type uB) [Category.{vB} B]
    (G : B ⥤ A) (F : A ⥤ B) (adj : G ⊣ F),
    (∀ (Y Y' : B) (f : Y ⟶ Y'),
      f ≫ adj.unit.app Y' = adj.unit.app Y ≫ F.map (G.map f)) ∧
    (∀ (X X' : A) (g : X ⟶ X'),
      G.map (F.map g) ≫ adj.counit.app X' = adj.counit.app X ≫ g)

/-- The right and left triangle identities in the source's printed order. -/
def TriangleIdentitiesStatement : Prop :=
  ∀ (A : Type uA) [Category.{vA} A] (B : Type uB) [Category.{vB} B]
    (G : B ⥤ A) (F : A ⥤ B) (adj : G ⊣ F),
    (∀ X : A, adj.unit.app (F.obj X) ≫ F.map (adj.counit.app X) =
      𝟙 (F.obj X)) ∧
    (∀ Y : B, G.map (adj.unit.app Y) ≫ adj.counit.app (G.obj Y) =
      𝟙 (G.obj Y))

/-- The forward and inverse Hom equivalence are the actual unit/counit formulas. -/
def HomEquivFormulasStatement : Prop :=
  ∀ (A : Type uA) [Category.{vA} A] (B : Type uB) [Category.{vB} B]
    (G : B ⥤ A) (F : A ⥤ B) (adj : G ⊣ F),
    (∀ (Y : B) (X : A) (h : G.obj Y ⟶ X),
      adj.homEquiv Y X h = adj.unit.app Y ≫ F.map h) ∧
    (∀ (Y : B) (X : A) (k : Y ⟶ F.obj X),
      (adj.homEquiv Y X).symm k = G.map k ≫ adj.counit.app X)

/-- Both explicit Hom maps are natural before imposing either triangle. -/
def HomMapNaturalityStatement : Prop :=
  ∀ (A : Type uA) [Category.{vA} A] (B : Type uB) [Category.{vB} B]
    (G : B ⥤ A) (F : A ⥤ B)
    (η : 𝟭 B ⟶ G ⋙ F) (ε : F ⋙ G ⟶ 𝟭 A),
    (∀ (Y Y' : B) (X X' : A) (f : Y' ⟶ Y) (g : X ⟶ X')
      (h : G.obj Y ⟶ X),
      η.app Y' ≫ F.map (G.map f ≫ h ≫ g) =
        f ≫ (η.app Y ≫ F.map h) ≫ F.map g) ∧
    (∀ (Y Y' : B) (X X' : A) (f : Y' ⟶ Y) (g : X ⟶ X')
      (k : Y ⟶ F.obj X),
      G.map (f ≫ k ≫ F.map g) ≫ ε.app X' =
        G.map f ≫ (G.map k ≫ ε.app X) ≫ g)

/-- Both triangles make the two explicit Hom maps mutually inverse. -/
def HomMapInverseIdentitiesStatement : Prop :=
  ∀ (A : Type uA) [Category.{vA} A] (B : Type uB) [Category.{vB} B]
    (G : B ⥤ A) (F : A ⥤ B)
    (η : 𝟭 B ⟶ G ⋙ F) (ε : F ⋙ G ⟶ 𝟭 A)
    (_right : ∀ X : A, η.app (F.obj X) ≫ F.map (ε.app X) = 𝟙 (F.obj X))
    (_left : ∀ Y : B, G.map (η.app Y) ≫ ε.app (G.obj Y) = 𝟙 (G.obj Y)),
    (∀ (Y : B) (X : A) (h : G.obj Y ⟶ X),
      G.map (η.app Y ≫ F.map h) ≫ ε.app X = h) ∧
    (∀ (Y : B) (X : A) (k : Y ⟶ F.obj X),
      η.app Y ≫ F.map (G.map k ≫ ε.app X) = k)

/-- Actual natural transformations satisfying both triangles yield an adjunction. -/
def AdjunctionFromUnitCounitStatement : Prop :=
  ∀ (A : Type uA) [Category.{vA} A] (B : Type uB) [Category.{vB} B]
    (G : B ⥤ A) (F : A ⥤ B)
    (η : 𝟭 B ⟶ G ⋙ F) (ε : F ⋙ G ⟶ 𝟭 A)
    (_right : ∀ X : A, η.app (F.obj X) ≫ F.map (ε.app X) = 𝟙 (F.obj X))
    (_left : ∀ Y : B, G.map (η.app Y) ≫ ε.app (G.obj Y) = 𝟙 (G.obj Y)),
    ∃ adj : G ⊣ F, adj.unit = η ∧ adj.counit = ε

/-- The seven native unit–counit statement components, in source order. -/
def UnitCounitStatements : Prop :=
  UnitCounitAtIdentitiesStatement.{vA, uA, vB, uB} ∧
    UnitCounitNaturalityStatement.{vA, uA, vB, uB} ∧
    TriangleIdentitiesStatement.{vA, uA, vB, uB} ∧
    HomEquivFormulasStatement.{vA, uA, vB, uB} ∧
    HomMapNaturalityStatement.{vA, uA, vB, uB} ∧
    HomMapInverseIdentitiesStatement.{vA, uA, vB, uB} ∧
    AdjunctionFromUnitCounitStatement.{vA, uA, vB, uB}

end Langlands.Renard.UnitCounit
