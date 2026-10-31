import Langlands.AlgebraicGeometry.Modules.ModuleSupport
import Langlands.AlgebraicGeometry.Modules.DerivedSections

/-! # Cohomology and zero detection for scheme modules with finite closed support -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Modules

/-- For an actual scheme module with finite closed support, all positive-degree cohomology
vanishes and global sections detect its vanishing, also for the `R`-module versions over
any affine base `Spec R`. -/
def FiniteClosedSupportCohomologyStatement : Prop :=
  ∀ (X : Scheme.{u}) (M : X.Modules),
    HasFiniteClosedSupport M →
    (∀ n : ℕ, IsZero ((DerivedSections.cohomology X (n + 1)).obj M)) ∧
    (IsZero ((DerivedSections.globalSections X).obj M) ↔ IsZero M) ∧
    ∀ (R : CommRingCat.{u}) (f : X ⟶ Spec R),
      (∀ n : ℕ, IsZero ((DerivedSections.relativeCohomology f (n + 1)).obj M)) ∧
      (IsZero ((DerivedSections.relativeGlobalSections f).obj M) ↔ IsZero M)

end Langlands.AlgebraicGeometry.Modules
