import Langlands.GroupScheme.Rational.SteinbergRootProduct
import Langlands.GroupScheme.Reductive.Semisimple

/-! # Closed immersion target for the supplied split Steinberg product -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- For a semisimple group over an arbitrary field with a supplied split pinning,
the underlying scheme morphism of the actual ordered root product
`SplitPinning.steinbergProduct e x n` is a closed immersion, for every ordering
of the simple roots and all supplied root maps and reflection representatives. -/
def SplitSteinbergImmersionStatement : Prop :=
  ∀ (k : Type u) [Field k]
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom]
    (p : SplitPinning G), IsSemisimple G →
    ∀ (r : ℕ) (e : Fin r ≃ p.base.support)
      (x : p.NormalizedSimpleRootParametrizations)
      (n : p.SimpleReflectionRepresentatives),
      IsClosedImmersion (SplitPinning.steinbergProduct e x n).left

end Langlands.GroupScheme
