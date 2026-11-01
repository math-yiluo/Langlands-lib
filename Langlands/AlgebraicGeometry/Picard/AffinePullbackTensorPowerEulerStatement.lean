import Langlands.AlgebraicGeometry.Modules.EulerCharacteristic
import Langlands.AlgebraicGeometry.Picard.LineBundlePullback
import Langlands.AlgebraicGeometry.Modules.Tensor
import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-! # Actual Euler values of pullback tensor powers along an affine morphism -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard

open Langlands.Scheme.Modules
open Langlands.AlgebraicGeometry.Modules.DerivedSections

/-- Affine pullback tensor powers have the Euler values of tensoring with
the actual structure-module pushforward. -/
def AffinePullbackTensorPowerEulerStatement : Prop :=
  ∀ (K : Type u) [Field K] (X Y : Scheme.{u})
    (f : X ⟶ Y), IsAffineHom f →
      ∀ (s : Y ⟶ Spec (CommRingCat.of K)) (L : LineBundle Y) (n : ℕ),
        let A := tensorPow ((Scheme.Modules.pullback f).obj L.obj) n
        let B := tensorObj (tensorPow L.obj n)
          ((Scheme.Modules.pushforward f).obj (structureSheaf X))
        (HasFiniteCohomology (f ≫ s) A ↔ HasFiniteCohomology s B) ∧
          (∀ (hA : HasFiniteCohomology (f ≫ s) A)
            (hB : HasFiniteCohomology s B),
            eulerCharacteristic (f ≫ s) A hA = eulerCharacteristic s B hB)

end Langlands.AlgebraicGeometry.Picard
