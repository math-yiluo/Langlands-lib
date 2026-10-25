import Langlands.HarmonicAnalysis.Distribution.Basic
import Mathlib.Topology.Algebra.Nonarchimedean.Basic
import Mathlib.Topology.Algebra.ConstMulAction
import Mathlib.Topology.Algebra.MulAction

/-!
# Anti-invariant distributions on homogeneous spaces vanish

A Haar-measure-free form of the positivity argument of Bernstein–Zelevinsky
(1976), Example 6.12, which verifies the orbitwise condition d) of
Theorem 6.10. Section 7.3 needs it on each conjugacy class when it applies
Theorem 6.13 with `σ` the transpose; condition d) of Theorem 6.13 itself is
orbit preservation, which §7.3 gets from conjugacy of transposed matrices.
-/

namespace Langlands.HarmonicAnalysis.Distribution

universe uG uX

/-- Let a sigma-compact, locally compact nonarchimedean group `G` act
continuously and transitively on a Hausdorff locally compact space `X`. If a
`G`-invariant distribution `D` on `X` satisfies `σ_* D = -D` for some
homeomorphism `σ` of `X`, then `D = 0`. No compatibility between `σ` and the
action is assumed. -/
def HomogeneousAntiInvariantVanishingStatement : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G] [NonarchimedeanGroup G]
      [LocallyCompactSpace G] [SigmaCompactSpace G]
    (X : Type uX) [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
      [MulAction G X] [ContinuousSMul G X] [MulAction.IsPretransitive G X]
    (σ : X ≃ₜ X) (D : Distribution X),
    (∀ g : G, pushforward (Homeomorph.smul g) D = D) →
    pushforward σ D = -D → D = 0

end Langlands.HarmonicAnalysis.Distribution
