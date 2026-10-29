import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Langlands.AlgebraicGeometry.Modules.DerivedSections

/-! # Higher direct images of quasi-coherent modules along an affine morphism vanish -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Modules

/-- For every affine morphism of schemes `f : X ⟶ S` and every quasi-coherent `𝒪_X`-module `M`,
the higher direct images `R^{q+1} f_* M` vanish in every positive degree. -/
def AffineQuasicoherentHigherDirectImageVanishingStatement : Prop :=
  ∀ (X S : Scheme.{u}) (f : X ⟶ S), IsAffineHom f →
    ∀ (M : X.Modules), M.IsQuasicoherent →
      ∀ q : ℕ, IsZero ((DerivedSections.higherDirectImage f (q + 1)).obj M)

end Langlands.AlgebraicGeometry.Modules
