import Langlands.AlgebraicGeometry.Modules.ModuleSupport
import Langlands.AlgebraicGeometry.Modules.DerivedSections

/-! # A finite-support Leray comparison for actual scheme modules

This file defines a proposition; it does not prove it.
-/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Modules

/-- When all higher direct images have finite closed support, total cohomology
is isomorphic to global sections of the higher direct images in every degree.
Only existence of an isomorphism of `R`-modules is asserted. -/
def FiniteClosedSupportLerayStatement : Prop :=
  ∀ (X Y : Scheme.{u}) (R : CommRingCat.{u})
    (f : X ⟶ Y) (g : Y ⟶ Spec R) (M : X.Modules),
    (∀ q : ℕ, HasFiniteClosedSupport ((DerivedSections.higherDirectImage f q).obj M)) →
    ∀ n : ℕ,
      Nonempty
        (((DerivedSections.relativeCohomology (f ≫ g) n).obj M) ≅
          (DerivedSections.relativeGlobalSections g).obj
            ((DerivedSections.higherDirectImage f n).obj M))

end Langlands.AlgebraicGeometry.Modules
