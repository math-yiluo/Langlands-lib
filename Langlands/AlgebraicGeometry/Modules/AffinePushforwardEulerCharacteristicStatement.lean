import Langlands.AlgebraicGeometry.Modules.EulerCharacteristic
import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-! # Euler characteristic and actual affine pushforward -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Modules.DerivedSections

/-- For an actual quasi-coherent sheaf, affine pushforward preserves finite
cohomology over a field and preserves its actual Euler characteristic. -/
def AffinePushforwardEulerCharacteristicStatement : Prop :=
  ∀ (K : Type u) [Field K] (X Y : Scheme.{u})
    (h : X ⟶ Y), IsAffineHom h →
      ∀ (g : Y ⟶ Spec (CommRingCat.of K)) (M : X.Modules),
        M.IsQuasicoherent →
          (HasFiniteCohomology (h ≫ g) M ↔
            HasFiniteCohomology g ((Scheme.Modules.pushforward h).obj M)) ∧
          (∀ (hM : HasFiniteCohomology (h ≫ g) M)
            (hP : HasFiniteCohomology g ((Scheme.Modules.pushforward h).obj M)),
            eulerCharacteristic (h ≫ g) M hM =
              eulerCharacteristic g ((Scheme.Modules.pushforward h).obj M) hP)

end Langlands.AlgebraicGeometry.Modules.DerivedSections
