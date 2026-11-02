import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.CategoryTheory.Limits.Preserves.Finite

/-! # Pullback of scheme modules along a flat morphism is exact -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Modules

/-- For every flat morphism of schemes `f : X ⟶ Y`, the pullback functor
`f^* : Y.Modules ⥤ X.Modules` on sheaves of modules preserves finite limits. Since `f^*` is an
additive left adjoint, it also preserves finite colimits, so this is exactness of `f^*`
(Stacks, Lemma 17.20.2, tag 02N4, for schemes). -/
def FlatPullbackExactStatement : Prop :=
  ∀ (X Y : Scheme.{u}) (f : X ⟶ Y),
    Flat f → PreservesFiniteLimits (Scheme.Modules.pullback f)

end Langlands.AlgebraicGeometry.Modules
