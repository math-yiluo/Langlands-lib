import Langlands.HarmonicAnalysis.Distribution.Basic
import Mathlib.Topology.Algebra.Nonarchimedean.Basic
import Mathlib.Topology.Algebra.ConstMulAction
import Mathlib.Topology.Algebra.MulAction

/-!
# Positive rational proportionality on compact open sets

An internal statement target strengthening the indicator comparison in the
proof plan for homogeneous anti-invariant distribution vanishing. The
motivation is Bernstein–Zelevinsky (1976), Example 6.12, printed p.56;
the precise positive rational assertion below is not stated in that source.
-/

namespace Langlands.HarmonicAnalysis.Distribution

universe uG uX

/-- An invariant algebraic distribution for a continuous transitive action of a
sigma-compact, locally compact nonarchimedean group takes positively rationally
proportional values on the indicators of any two nonempty compact clopen sets.
This definition states the proposition without proving it. -/
def HomogeneousIndicatorProportionalityStatement : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G] [NonarchimedeanGroup G]
      [LocallyCompactSpace G] [SigmaCompactSpace G]
    (X : Type uX) [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
      [MulAction G X] [ContinuousSMul G X] [MulAction.IsPretransitive G X]
    (D : Distribution X),
    (∀ g : G, pushforward (Homeomorph.smul g) D = D) →
    ∀ (U V : Set X) (hU : IsClopen U) (hcU : IsCompact U)
      (hV : IsClopen V) (hcV : IsCompact V),
      U.Nonempty → V.Nonempty →
      ∃ q : ℚ, 0 < q ∧
        D (Langlands.Hecke.TestFunction.characteristic hU hcU) =
          (q : ℂ) * D (Langlands.Hecke.TestFunction.characteristic hV hcV)

end Langlands.HarmonicAnalysis.Distribution
