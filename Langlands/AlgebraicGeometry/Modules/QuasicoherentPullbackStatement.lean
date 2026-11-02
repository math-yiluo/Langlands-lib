import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent

/-! # Pullback of scheme modules preserves quasi-coherence -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Modules

/-- For every morphism of schemes `f : X ⟶ Y` and every quasi-coherent `𝒪_Y`-module `M`,
the pullback `f^* M` is a quasi-coherent `𝒪_X`-module. -/
def QuasicoherentPullbackStatement : Prop :=
  ∀ (X Y : Scheme.{u}) (f : X ⟶ Y) (M : Y.Modules),
    M.IsQuasicoherent →
      ((Scheme.Modules.pullback f).obj M).IsQuasicoherent

end Langlands.AlgebraicGeometry.Modules
