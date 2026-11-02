import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Langlands.AlgebraicGeometry.Modules.DerivedSections

/-!
# Quasi-coherence of higher direct images

This file states that the higher direct images of a quasi-coherent module along a
quasi-compact separated morphism of schemes are quasi-coherent, in every degree.
-/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Modules

/-- For every quasi-compact separated morphism of schemes `f : X ⟶ Y`, every quasi-coherent
`𝒪_X`-module `M` and every `n : ℕ`, the higher direct image `Rⁿ f_* M` is a quasi-coherent
`𝒪_Y`-module. This definition states a proposition and does not prove it. -/
def HigherDirectImageQuasicoherentStatement : Prop :=
  ∀ (X Y : Scheme.{u}) (f : X ⟶ Y),
    QuasiCompact f → IsSeparated f →
      ∀ (M : X.Modules), M.IsQuasicoherent → ∀ n : ℕ,
        ((DerivedSections.higherDirectImage f n).obj M).IsQuasicoherent

end Langlands.AlgebraicGeometry.Modules
