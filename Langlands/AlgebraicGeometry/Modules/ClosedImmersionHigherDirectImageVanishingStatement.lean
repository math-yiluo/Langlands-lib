import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Langlands.AlgebraicGeometry.Modules.DerivedSections

/-! # Higher direct images along a closed immersion vanish -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Modules

/-- For every closed immersion of schemes `i : X ⟶ Y` and every `𝒪_X`-module `M`, the higher
direct images `R^{q+1} i_* M` vanish in every positive degree. -/
def ClosedImmersionHigherDirectImageVanishingStatement : Prop :=
  ∀ (X Y : Scheme.{u}) (i : X ⟶ Y), IsClosedImmersion i →
    ∀ (M : X.Modules) (q : ℕ),
      IsZero ((DerivedSections.higherDirectImage i (q + 1)).obj M)

end Langlands.AlgebraicGeometry.Modules
