import Mathlib.AlgebraicGeometry.AffineScheme
import Langlands.AlgebraicGeometry.Modules.DerivedSections

/-! # Higher cohomology of quasi-coherent modules on affine schemes vanishes -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Modules

/-- For every affine scheme `X` and every quasi-coherent `𝒪_X`-module `M`, the higher
cohomology of `M` vanishes, both as `Γ(X, ⊤)`-modules and as `R`-modules for every
morphism `X ⟶ Spec R`. -/
def AffineQuasicoherentCohomologyVanishingStatement : Prop :=
  ∀ (X : Scheme.{u}), IsAffine X → ∀ (M : X.Modules), M.IsQuasicoherent →
    ∀ n : ℕ,
      IsZero ((DerivedSections.cohomology X (n + 1)).obj M) ∧
      ∀ (R : CommRingCat.{u}) (g : X ⟶ Spec R),
        IsZero ((DerivedSections.relativeCohomology g (n + 1)).obj M)

end Langlands.AlgebraicGeometry.Modules
