import Langlands.AlgebraicGeometry.Modules.RelativeFlatness
import Mathlib.AlgebraicGeometry.Modules.Tilde

/-! # The affine relative flatness criterion -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Modules

/-- The associated sheaf on `Spec B` is flat over `Spec R` exactly when the original
module is flat over `R` through the given ring map. -/
def AffineRelativeFlatnessStatement : Prop :=
  ∀ (R B : CommRingCat.{u}) (φ : R ⟶ B) (M : ModuleCat.{u} B),
    letI := φ.hom.toAlgebra
    letI : Module R M := Module.compHom M φ.hom
    IsFlatOver (Spec.map φ) (tilde M) ↔ Module.Flat R M

end Langlands.AlgebraicGeometry.Modules
