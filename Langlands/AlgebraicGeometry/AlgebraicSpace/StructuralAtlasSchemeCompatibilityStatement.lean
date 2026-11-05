import Langlands.AlgebraicGeometry.AlgebraicSpace.StructuralAtlasGeometry

/-! # Structural atlas geometry agrees with scheme geometry on actual schemes

For an actual scheme `U` over a scheme base `S`, viewed as an algebraic space, each of the
three published structural atlas predicates is equivalent to the corresponding Mathlib
property of the structure morphism `U.hom`. This is the scheme case of the etale chart
criteria of Stacks Project Lemma 67.22.1 (Tag 03MJ), Lemma 67.37.4 (Tag 03ZB) and
Lemma 67.28.4 (Tag 03XO).
-/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

/-- For every actual scheme `U` over every scheme `S`, its embedded algebraic space is
smooth, locally of finite presentation, or locally of finite type over the base in the
one-atlas sense exactly when `U.hom` has the corresponding Mathlib property. The three
equivalences are independent conjuncts. -/
def StructuralAtlasSchemeCompatibilityStatement : Prop :=
  ∀ (S : Scheme.{u}) (U : Over S),
    (SmoothOverBase ((schemeToSpace S).obj U) ↔
      Smooth U.hom) ∧
    (LocallyOfFinitePresentationOverBase ((schemeToSpace S).obj U) ↔
      LocallyOfFinitePresentation U.hom) ∧
    (LocallyOfFiniteTypeOverBase ((schemeToSpace S).obj U) ↔
      LocallyOfFiniteType U.hom)

end Langlands.AlgebraicGeometry.AlgebraicSpace
