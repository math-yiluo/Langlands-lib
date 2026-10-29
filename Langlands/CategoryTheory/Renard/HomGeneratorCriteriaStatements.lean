import Langlands.CategoryTheory.Renard.HomObjectProperties
import Mathlib.CategoryTheory.Generator.Preadditive

/-!
# Renard's generator comparisons and projective nonzero-Hom criterion

The first two propositions compare Renard's faithful-Hom definitions with
Mathlib's separators and coseparators. The third states the explicit
projective progenerator criterion in Renard A.VIII.2.
-/

open CategoryTheory

universe v u

namespace Langlands.Renard

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Compare Renard generation with the native parallel-morphism separator test. -/
def HomGeneratorComparisonStatement (P : C) : Prop :=
  HomGenerator P ↔ CategoryTheory.IsSeparator P

/-- Compare Renard cogeneration with the native parallel-morphism coseparator test. -/
def HomCogeneratorComparisonStatement (P : C) : Prop :=
  HomCogenerator P ↔ CategoryTheory.IsCoseparator P

/-- A projective object is a progenerator exactly when it maps nontrivially to
every nonzero object, as in Renard A.VIII.2. -/
def ProjectiveProgeneratorCriterionStatement (P : C) : Prop :=
  HomProjective P →
    (HomProgenerator P ↔
      ∀ Y : C, ¬CategoryTheory.Limits.IsZero Y → ∃ f : P ⟶ Y, f ≠ 0)

/-- The two derived comparisons followed by the source progenerator criterion. -/
def HomGeneratorCriteriaStatement (P : C) : Prop :=
  HomGeneratorComparisonStatement P ∧
    HomCogeneratorComparisonStatement P ∧
    ProjectiveProgeneratorCriterionStatement P

end Langlands.Renard
