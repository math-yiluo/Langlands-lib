import Langlands.AbelianScheme.LieFunctor

/-! # Additivity target for the relative Lie differential -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.CommGroupScheme

/-- The actual differential preserves pointwise addition of group-scheme homomorphisms. -/
def LieAdditivityStatement (S : AlgebraicGeometry.Scheme.{u}) : Prop :=
  ∀ (G H : CommGroupScheme S) (f g : G ⟶ H),
    lieMap (f + g) = lieMap f + lieMap g

end Langlands.CommGroupScheme
