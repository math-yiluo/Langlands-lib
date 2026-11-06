import Langlands.AlgebraicGeometry.AlgebraicSpace.StructuralCompactness

/-! # Structural compactness and finite type on represented schemes

The three compatibility equivalences compare the published structural predicates
on an embedded scheme with compactness of that scheme and the Mathlib properties
of its structure morphism. This module states the proposition and supplies no proof.
-/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

/-- Absolute quasi-compactness, structural quasi-compactness and structural finite type
agree with the corresponding scheme properties for every actual scheme over every
scheme base. `CompactSpace` imposes no Hausdorff assumption. -/
def StructuralCompactnessSchemeCompatibilityStatement : Prop :=
  ∀ (S : Scheme.{u}) (U : Over S),
    (IsQuasiCompact ((schemeToSpace S).obj U) ↔
      CompactSpace U.left) ∧
    (QuasiCompactOverBase ((schemeToSpace S).obj U) ↔
      QuasiCompact U.hom) ∧
    (FiniteTypeOverBase ((schemeToSpace S).obj U) ↔
      (LocallyOfFiniteType U.hom ∧ QuasiCompact U.hom))

end Langlands.AlgebraicGeometry.AlgebraicSpace
