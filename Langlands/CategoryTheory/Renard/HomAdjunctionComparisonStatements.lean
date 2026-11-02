import Langlands.CategoryTheory.Renard.AdjunctionHom
import Mathlib.CategoryTheory.Adjunction.Basic

/-!
# Renard A.V: comparison of the two definitions of adjunction

The component equations retain the chosen natural isomorphism and the
independent Hom universes of both categories.
-/

open CategoryTheory Opposite
open Langlands.Renard.AdjunctionHom

namespace Langlands.Renard.HomAdjunctionComparison

universe vA uA vB uB

/-- A native adjunction gives the source Hom isomorphism with both exact maps. -/
def NativeToHomStatement : Prop :=
  ∀ (A : Type uA) [Category.{vA} A] (B : Type uB) [Category.{vB} B]
    (G : B ⥤ A) (F : A ⥤ B) (adj : G ⊣ F),
    ∃ theta : rightHomBifunctor F ≅ leftHomBifunctor G,
      (∀ (X : A) (Y : B) (k : Y ⟶ F.obj X),
        (theta.hom.app (X, op Y) (ULift.up k)).down =
          (adj.homEquiv Y X).symm k) ∧
      (∀ (X : A) (Y : B) (h : G.obj Y ⟶ X),
        (theta.inv.app (X, op Y) (ULift.up h)).down =
          adj.homEquiv Y X h)

/-- Every supplied source Hom isomorphism gives a native adjunction preserving it. -/
def HomToNativeStatement : Prop :=
  ∀ (A : Type uA) [Category.{vA} A] (B : Type uB) [Category.{vB} B]
    (G : B ⥤ A) (F : A ⥤ B)
    (theta : rightHomBifunctor F ≅ leftHomBifunctor G),
    ∃ adj : G ⊣ F,
      (∀ (X : A) (Y : B) (k : Y ⟶ F.obj X),
        (theta.hom.app (X, op Y) (ULift.up k)).down =
          (adj.homEquiv Y X).symm k) ∧
      (∀ (X : A) (Y : B) (h : G.obj Y ⟶ X),
        (theta.inv.app (X, op Y) (ULift.up h)).down =
          adj.homEquiv Y X h)

/-- Existence of the source Hom isomorphism is equivalent to native adjointness. -/
def HomAdjunctionIffNativeStatement : Prop :=
  ∀ (A : Type uA) [Category.{vA} A] (B : Type uB) [Category.{vB} B]
    (G : B ⥤ A) (F : A ⥤ B),
    HomAdjunction G F ↔ Nonempty (G ⊣ F)

/-- The two exact component comparisons and their existential consequence. -/
def HomAdjunctionComparisonStatements : Prop :=
  NativeToHomStatement.{vA, uA, vB, uB} ∧
    HomToNativeStatement.{vA, uA, vB, uB} ∧
    HomAdjunctionIffNativeStatement.{vA, uA, vB, uB}

end Langlands.Renard.HomAdjunctionComparison
