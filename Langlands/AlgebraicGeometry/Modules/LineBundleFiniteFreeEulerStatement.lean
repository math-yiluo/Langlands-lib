import Langlands.AlgebraicGeometry.Modules.EulerCharacteristic
import Langlands.AlgebraicGeometry.Picard.LineBundle
import Langlands.AlgebraicGeometry.Modules.Tensor
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free

/-! # Euler characteristics after tensoring with a finite free sheaf -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Modules.DerivedSections

open Langlands.Scheme.Modules

/-- Tensoring a line bundle with the actual free sheaf on `r` generators
preserves finite cohomology and multiplies its Euler value by `r`. -/
def LineBundleFiniteFreeEulerStatement : Prop :=
  ∀ (K : Type u) [Field K] (X : Scheme.{u})
    (s : X ⟶ Spec (CommRingCat.of K)) (L : Picard.LineBundle X) (r : ℕ)
    (hL : HasFiniteCohomology s L.obj),
    let M := tensorObj L.obj
      (SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin r)))
    HasFiniteCohomology s M ∧
      ∀ hM : HasFiniteCohomology s M,
        eulerCharacteristic s M hM = (r : ℤ) * eulerCharacteristic s L.obj hL

end Langlands.AlgebraicGeometry.Modules.DerivedSections
