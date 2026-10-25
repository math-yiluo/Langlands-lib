import Langlands.Representation.Induction.Definitions
import Mathlib.Basic.Complex.Basic

namespace Langlands.Induction

universe uG uV uW

/-- Compact induction from a closed subgroup carries a surjective intertwiner of
smooth complex representations to a surjective map, when compact open subgroups
are cofinal among open subgroups. This is a proposition target. -/
def CompactInductionSurjectivityStatement : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G],
    (∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G,
      IsCompact (L : Set G) ∧ L.toSubgroup ≤ K.toSubgroup) →
    ∀ (H : Subgroup G), IsClosed (H : Set G) →
    ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (W : Type uW) [AddCommGroup W] [Module ℂ W]
      (sigma : Representation ℂ H V) (tau : Representation ℂ H W),
      IsSmooth sigma → IsSmooth tau →
      ∀ T : sigma.IntertwiningMap tau, Function.Surjective T →
        Function.Surjective (compactInducedMap H T)

end Langlands.Induction
