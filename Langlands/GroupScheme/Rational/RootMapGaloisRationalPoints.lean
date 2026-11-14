import Langlands.GroupScheme.Rational.SteinbergRationalGaloisTransport

/-! # Galois transport of rational values of compatible root maps -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
set_option autoImplicit false

namespace SplitPinning

variable (k K : Type u) [Field k] [Field K] [Algebra k K]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance rootMapGaloisRationalPointsIsAffineHom :
    IsAffineHom ((GroupScheme.baseChange (algebraBaseMap k K)).obj G).X.hom := by
  change IsAffineHom (pullback.snd G.X.hom (algebraBaseMap k K))
  infer_instance

variable {p : SplitPinning ((GroupScheme.baseChange (algebraBaseMap k K)).obj G)}

/-- Whole-map compatibility transports every rational value of a root map: coefficient
conjugation by `σ` sends `x_a(c)` to `x_{ρ σ a}(σ c)`. -/
theorem RootMapsGaloisCompatible.rationalPoint
    {x : p.NormalizedSimpleRootParametrizations}
    {ρ : (K ≃ₐ[k] K) →* Equiv.Perm p.base.support}
    (hx : RootMapsGaloisCompatible k K p x ρ) (σ : K ≃ₐ[k] K) (a : p.base.support)
    (c : K) :
    GaloisPointComparison.rationalConjugate k K G σ
        ((x a).toRootParametrization.rationalPoint c) =
      (x (ρ σ a)).toRootParametrization.rationalPoint (σ c) :=
  RootMapsGaloisCompatible.rationalPoints k K G x ρ hx σ a c

end SplitPinning

end Langlands.GroupScheme
