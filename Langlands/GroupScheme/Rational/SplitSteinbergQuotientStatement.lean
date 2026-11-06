import Langlands.GroupScheme.Rational.SteinbergRootProduct
import Langlands.GroupScheme.Rational.ClassFunctions
import Langlands.GroupScheme.SimplyConnected.Basic

/-! # Statement: the canonical class quotient on the supplied split Steinberg product -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- **Steinberg's cross-section isomorphism for the canonical quotient.** For a simply
connected group with supplied split pinning over an arbitrary field, the actual ordered
product `SplitPinning.steinbergProduct e x n` from standard affine `r`-space, followed by
the canonical class quotient map `ClassFunctions.rho G`, is an isomorphism in
`Over (Spec k)`, for every simple-root ordering `e`, normalized simple-root maps `x` and
simple-reflection representatives `n`. -/
def SplitSteinbergQuotientStatement : Prop :=
  ∀ (k : Type u) [Field k]
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom]
    (p : SplitPinning G), IsSimplyConnected G →
    ∀ (r : ℕ) (e : Fin r ≃ p.base.support)
      (x : p.NormalizedSimpleRootParametrizations)
      (n : p.SimpleReflectionRepresentatives),
      IsIso (SplitPinning.steinbergProduct e x n ≫ ClassFunctions.rho G)

end Langlands.GroupScheme
