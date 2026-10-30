import Langlands.CategoryTheory.Renard.SimpleSupport
import Langlands.CategoryTheory.Renard.LocallyFiniteType
import Langlands.CategoryTheory.RenardGrothendieckAxioms
import Mathlib.CategoryTheory.Preadditive.Biproducts

/-!
# Renard A.IX: disjoint supports and canonical subobject maps

Proposition targets for the unnumbered assertion on printed268/PDF274
of the French edition dated 9 July 2026. Hom vanishing uses actual
supported objects. The intersection and binary-sum components expose
the source's consequence for any actual supported subobjects.
-/

universe w v u

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Renard

/-- Every actual morphism between objects with disjoint simple supports
vanishes, in the original source context. -/
@[pp_with_univ]
def SimpleSupportHomOrthogonalityStatement
    (C : Type u) [Category.{v} C] [Abelian C] : Prop :=
  IsSourceGrothendieck.{w} C → SourceAB6 C →
    ∀ S T : Set (ObjectClass C), S ⊆ simpleClasses C →
      T ⊆ simpleClasses C → Disjoint S T →
        ∀ X Y : C, HasSimpleSupport S X → HasSimpleSupport T Y →
          ∀ f : X ⟶ Y, f = 0

/-- Internal form of the source intersection assertion for any two
actual supported subobjects of a common ambient object. -/
@[pp_with_univ]
def SimpleSupportSubobjectIntersectionStatement
    (C : Type u) [Category.{v} C] [Abelian C] : Prop :=
  IsSourceGrothendieck.{w} C → SourceAB6 C →
    ∀ S T : Set (ObjectClass C), S ⊆ simpleClasses C →
      T ⊆ simpleClasses C → Disjoint S T →
        ∀ (X : C) (P Q : Subobject X),
          HasSimpleSupport S (P : C) → HasSimpleSupport T (Q : C) →
            P ⊓ Q = ⊥

/-- The actual map from the binary biproduct of supported subobjects
into their common ambient object is monic when their supports are disjoint. -/
@[pp_with_univ]
def SimpleSupportSubobjectBiproductMonoStatement
    (C : Type u) [Category.{v} C] [Abelian C] : Prop :=
  IsSourceGrothendieck.{w} C → SourceAB6 C →
    ∀ S T : Set (ObjectClass C), S ⊆ simpleClasses C →
      T ⊆ simpleClasses C → Disjoint S T →
        ∀ (X : C) (P Q : Subobject X),
          HasSimpleSupport S (P : C) → HasSimpleSupport T (Q : C) →
            Mono (biprod.desc P.arrow Q.arrow)

/-- Hom orthogonality and its explicit consequences for actual supported
subobjects, retaining the complete source hypotheses in every component. -/
@[pp_with_univ]
def SimpleSupportOrthogonalityStatement
    (C : Type u) [Category.{v} C] [Abelian C] : Prop :=
  SimpleSupportHomOrthogonalityStatement.{w} C ∧
    SimpleSupportSubobjectIntersectionStatement.{w} C ∧
      SimpleSupportSubobjectBiproductMonoStatement.{w} C

end Langlands.Renard
