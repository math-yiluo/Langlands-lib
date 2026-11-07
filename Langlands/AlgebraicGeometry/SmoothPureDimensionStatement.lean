import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Langlands.AlgebraicGeometry.SchemePureDimensionFibers

/-! # Smooth chart dimension and pure dimension of actual fibres -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

/-- Fixed standard-smooth chart dimension over a field is the dimension of
every actual irreducible component. The empty scheme is allowed. -/
def FieldSmoothPureDimensionStatement : Prop :=
  ∀ (k : Type u) [Field k] (X : Scheme.{u})
    (f : X ⟶ Spec (CommRingCat.of k)) (n : ℕ),
    SmoothOfRelativeDimension n f → SchemeFiberGeometry.HasPureDimension X n

/-- Every actual residue-field fibre of a morphism smooth of fixed chart
dimension has that pure dimension. Empty fibres are allowed. -/
def SmoothPureDimensionFibersStatement : Prop :=
  ∀ (X Y : Scheme.{u}) (f : X ⟶ Y) (n : ℕ),
    SmoothOfRelativeDimension n f → SchemeFiberGeometry.HasPureDimensionFibers n f

/-- The field and actual-fibre comparisons for arbitrary common universe. -/
def SmoothPureDimensionStatement : Prop :=
  FieldSmoothPureDimensionStatement.{u} ∧ SmoothPureDimensionFibersStatement.{u}

end Langlands.AlgebraicGeometry
