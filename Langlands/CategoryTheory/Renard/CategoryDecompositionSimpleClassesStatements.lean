import Langlands.CategoryTheory.RenardCategoryDecomposition
import Langlands.CategoryTheory.Renard.CompositionChains

/-!
# Renard A.IX: simple classes of a category decomposition

The source's first assertion after the decomposition definition is that the
simple classes form the disjoint union of the component simple classes
(printed page 268 / PDF page 274, French edition dated 9 July 2026).

These derived statement targets make internal simplicity and the images of
component classes in the ambient class quotient explicit. They use the actual
published decomposition condition. No repleteness or abelian structure on the
full subcategories is assumed, and no proof is supplied here.
-/

universe w v u

open CategoryTheory

namespace Langlands.Renard

variable (C : Type u) [Category.{v} C] [Abelian C]

/-- Internal prerequisite: under an actual category decomposition, simplicity
in each full subcategory agrees with simplicity of the ambient object. -/
def CategoryDecompositionSimplicityStatement : Prop :=
  ∀ (I : Type w) (P : I → ObjectProperty C), IsCategoryDecomposition P →
    ∀ (i : I) (X : (P i).FullSubcategory), Simple X ↔ Simple X.obj

/-- Explicit class-image form of the source disjoint union: an ambient class
is simple exactly when it has an internally simple component representative
in exactly one block. The object representative is not asserted unique. -/
def CategoryDecompositionSimplePartitionStatement : Prop :=
  ∀ (I : Type w) (P : I → ObjectProperty C), IsCategoryDecomposition P →
    ∀ q : ObjectClass C, q ∈ simpleClasses C ↔
      ∃! i : I, ∃ X : (P i).FullSubcategory, Simple X ∧ objectClass X.obj = q

/-- The internal simplicity comparison and the explicit simple-class
partition target for an actual category decomposition. -/
def CategoryDecompositionSimpleClassesStatement : Prop :=
  CategoryDecompositionSimplicityStatement.{w} C ∧
    CategoryDecompositionSimplePartitionStatement.{w} C

end Langlands.Renard
