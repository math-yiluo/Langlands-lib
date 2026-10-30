import Langlands.CategoryTheory.Renard.SimpleSupport
import Langlands.CategoryTheory.Renard.LocallyFiniteType
import Langlands.CategoryTheory.RenardGrothendieckAxioms
import Mathlib.CategoryTheory.Abelian.SerreClass.Basic
import Mathlib.CategoryTheory.Abelian.Subcategory

/-!
# Renard A.IX: finite closure and abelianness of supported objects

Proposition targets for the unnumbered assertion on printed268/PDF274 of
the French edition dated 9 July 2026. The actual public supported full
subcategory is used throughout. Finite-product closure and exactness of
the inclusion are explicit internal consequences needed to realize the
source assertion with the inherited category and preadditive structure.
-/

universe w v u

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Renard

/-- The support predicate contains zero and is closed under subobjects,
quotients and extensions, in the original source context. -/
@[pp_with_univ]
def SimpleSupportSerreStatement
    (C : Type u) [Category.{v} C] [Abelian C] : Prop :=
  IsSourceGrothendieck.{w} C → SourceAB6 C →
    ∀ S : Set (ObjectClass C), S ⊆ simpleClasses C →
      (simpleSupportObjects S).IsSerreClass

/-- Internal finite-product closure, made explicit for the corrected
abelian full-subcategory criterion. -/
@[pp_with_univ]
def SimpleSupportFiniteProductsStatement
    (C : Type u) [Category.{v} C] [Abelian C] : Prop :=
  IsSourceGrothendieck.{w} C → SourceAB6 C →
    ∀ S : Set (ObjectClass C), S ⊆ simpleClasses C →
      (simpleSupportObjects S).IsClosedUnderFiniteProducts

/-- Renard's actual full supported subcategory admits an abelian structure
on its inherited category and inherited preadditive structure. -/
@[pp_with_univ]
def SimpleSupportAbelianStatement
    (C : Type u) [Category.{v} C] [Abelian C] : Prop :=
  IsSourceGrothendieck.{w} C → SourceAB6 C →
    ∀ S : Set (ObjectClass C), S ⊆ simpleClasses C →
      ∃ a : Abelian (SimpleSupportSubcategory S),
        a.toPreadditive = Preadditive.fullSubcategory (simpleSupportObjects S)

/-- Internal exactness of the actual inclusion, expressed as preservation
of finite limits and finite colimits. -/
@[pp_with_univ]
def SimpleSupportInclusionExactStatement
    (C : Type u) [Category.{v} C] [Abelian C] : Prop :=
  IsSourceGrothendieck.{w} C → SourceAB6 C →
    ∀ S : Set (ObjectClass C), S ⊆ simpleClasses C →
      PreservesFiniteLimits (simpleSupportInclusion S) ∧
        PreservesFiniteColimits (simpleSupportInclusion S)

/-- The finite closure and abelian-subcategory assertion, with the two
explicit internal realization consequences. -/
@[pp_with_univ]
def SimpleSupportFiniteClosureStatement
    (C : Type u) [Category.{v} C] [Abelian C] : Prop :=
  SimpleSupportSerreStatement.{w} C ∧
    SimpleSupportFiniteProductsStatement.{w} C ∧
      SimpleSupportAbelianStatement.{w} C ∧
        SimpleSupportInclusionExactStatement.{w} C

end Langlands.Renard
