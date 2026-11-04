import Langlands.AlgebraicGeometry.AffineSchemeScalarExtension
import Langlands.AlgebraicGeometry.SchemeFiberBaseChange

/-! # Pure dimension and base change for affine finite-type morphisms -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.SchemeFiberGeometry

/-- Pure dimension of an affine scheme locally of finite type over a field
is preserved and reflected by every extension of that field. -/
def FiniteTypeAffineSchemeFieldExtensionPureDimensionInvariance : Prop :=
  ∀ (k K : Type u) [Field k] [Field K] [Algebra k K]
    (X : Scheme.{u}) [IsAffine X] (f : X ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType f] (d : ℕ),
    HasPureDimension X d ↔
      HasPureDimension (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) d

/-- At each point of an arbitrary cartesian base change of an affine
locally finite-type morphism, the two actual fibres have the same pure dimension. -/
def AffineFiniteTypeFiberPureDimensionBaseChange : Prop :=
  ∀ (P X Y Z : Scheme.{u}) (a : P ⟶ X) (b : P ⟶ Y)
    (f : X ⟶ Z) (g : Y ⟶ Z) [IsAffineHom f] [LocallyOfFiniteType f]
    (_ : IsPullback a b f g) (y : Y) (d : ℕ),
    HasPureDimension (b.fiber y) d ↔ HasPureDimension (f.fiber (g y)) d

/-- Arbitrary base change preserves pure-dimensional fibres of an affine
locally finite-type morphism, and a surjective base change also reflects them. -/
def AffineFiniteTypePureDimensionFibersBaseChange : Prop :=
  ∀ (P X Y Z : Scheme.{u}) (a : P ⟶ X) (b : P ⟶ Y)
    (f : X ⟶ Z) (g : Y ⟶ Z) [IsAffineHom f] [LocallyOfFiniteType f]
    (_ : IsPullback a b f g) (d : ℕ),
    (HasPureDimensionFibers d f → HasPureDimensionFibers d b) ∧
      (Surjective g → (HasPureDimensionFibers d b ↔ HasPureDimensionFibers d f))

/-- Grouped scalar-extension and fibre comparisons for affine finite-type morphisms. -/
def AffineSchemePureDimensionComparisons : Prop :=
  FiniteTypeAffineSchemeFieldExtensionPureDimensionInvariance.{u} ∧
    AffineFiniteTypeFiberPureDimensionBaseChange.{u} ∧
    AffineFiniteTypePureDimensionFibersBaseChange.{u}

end Langlands.AlgebraicGeometry.SchemeFiberGeometry
