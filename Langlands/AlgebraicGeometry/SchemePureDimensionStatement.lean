import Langlands.AlgebraicGeometry.SchemePureDimensionFibers
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-! # Pure dimension of arbitrary locally finite-type schemes under base change -/

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.SchemeFiberGeometry

/-- Pure dimension is local on every actual open cover of a scheme locally
of finite type over a field. The cover index has an independent universe. -/
def LocallyFiniteTypePureDimensionOpenCover : Prop :=
  ∀ (k : Type u) [Field k] (X : Scheme.{u})
    (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f]
    (ι : Type v) (U : ι → X.Opens) (_ : ∀ x : X, ∃ i, x ∈ U i) (d : ℕ),
    HasPureDimension X d ↔ ∀ i, HasPureDimension (U i).toScheme d

/-- Every ground-field extension preserves and reflects pure dimension of an
arbitrary scheme locally of finite type over the original field. -/
def LocallyFiniteTypeSchemeFieldExtensionPureDimensionInvariance : Prop :=
  ∀ (k K : Type u) [Field k] [Field K] [Algebra k K]
    (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType f] (d : ℕ),
    HasPureDimension X d ↔
      HasPureDimension (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) d

/-- Each actual fibre in an arbitrary cartesian base change of a locally
finite-type scheme morphism has the pure dimension of the original fibre. -/
def LocallyFiniteTypeFiberPureDimensionBaseChange : Prop :=
  ∀ (P X Y Z : Scheme.{u}) (a : P ⟶ X) (b : P ⟶ Y)
    (f : X ⟶ Z) (g : Y ⟶ Z) [LocallyOfFiniteType f]
    (_ : IsPullback a b f g) (y : Y) (d : ℕ),
    HasPureDimension (b.fiber y) d ↔ HasPureDimension (f.fiber (g y)) d

/-- Arbitrary base change preserves pure-dimensional fibres of a locally
finite-type morphism, and a surjective base change also reflects them. -/
def LocallyFiniteTypePureDimensionFibersBaseChange : Prop :=
  ∀ (P X Y Z : Scheme.{u}) (a : P ⟶ X) (b : P ⟶ Y)
    (f : X ⟶ Z) (g : Y ⟶ Z) [LocallyOfFiniteType f]
    (_ : IsPullback a b f g) (d : ℕ),
    (HasPureDimensionFibers d f → HasPureDimensionFibers d b) ∧
      (Surjective g → (HasPureDimensionFibers d b ↔ HasPureDimensionFibers d f))

/-- Grouped locality, scalar-extension, and actual-fibre comparisons.
None of the schemes or morphisms is required to be affine or separated. -/
def SchemePureDimensionComparisons : Prop :=
  LocallyFiniteTypePureDimensionOpenCover.{u, v} ∧
    LocallyFiniteTypeSchemeFieldExtensionPureDimensionInvariance.{u} ∧
    LocallyFiniteTypeFiberPureDimensionBaseChange.{u} ∧
    LocallyFiniteTypePureDimensionFibersBaseChange.{u}

end Langlands.AlgebraicGeometry.SchemeFiberGeometry
