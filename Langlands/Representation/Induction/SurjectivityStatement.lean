import Langlands.Representation.Induction.Definitions
import Mathlib.Basic.Complex.Basic

namespace Langlands.Induction

universe uG uV uW

/-- Smooth induction from a closed subgroup carries a surjective intertwiner of
smooth complex representations to a surjective map, when compact open subgroups
are cofinal among open subgroups. This is a proposition target. -/
def SmoothInductionSurjectivityStatement : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G],
    (∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G,
      IsCompact (L : Set G) ∧ L.toSubgroup ≤ K.toSubgroup) →
    ∀ (P : Subgroup G), IsClosed (P : Set G) →
    ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (W : Type uW) [AddCommGroup W] [Module ℂ W]
      (sigma : Representation ℂ P V) (tau : Representation ℂ P W),
      IsSmooth sigma → IsSmooth tau →
      ∀ q : sigma.IntertwiningMap tau, Function.Surjective q →
        Function.Surjective (smoothInducedMap P q)

end Langlands.Induction
