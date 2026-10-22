import Langlands.Global.ProfiniteIntegerRing
import Langlands.Weil.Pullback

/-!
# Normalized comparison of the two profinite-integer constructions
-/

namespace Langlands.Global

/-- The residue scalar ring's additive group is continuously equivalent to the
existing profinite completion of the integer group, with the canonical integer
maps identified. This proposition is a statement target, not a chosen bridge. -/
def ProfiniteIntegerCompletionComparison : Prop :=
  ∃ e : Multiplicative ProfiniteIntegerRing ≃* Langlands.Weil.ProfiniteIntegers,
    Continuous e ∧ Continuous e.symm ∧
      ∀ z : ℤ,
        e (Multiplicative.ofAdd (ProfiniteIntegerRing.intCastHom z)) =
          Langlands.Weil.frobenius (Multiplicative.ofAdd z)

end Langlands.Global
