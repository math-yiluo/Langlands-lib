import Langlands.Global.Factors.WeilPoleRegionUnitaryProof
import Langlands.Global.Factors.WeilPoleRegionNonJuxtaposedProof

/-!
# The Weil-side pole-region noncancellation of Henniart 1986, Proposition 4.5(i)

Proof of `Langlands.Global.WeilPairPoleRegionStatement` from its two conjuncts.
-/

universe u v w

namespace Langlands.Global

/-- **Henniart 1986, Proposition 4.5(i), Weil side.** Both pole-region cases hold: the
essentially unitary case and the non-juxtaposed case. -/
theorem weilPairPoleRegionStatement : WeilPairPoleRegionStatement.{u, v, w} :=
  ⟨essentiallyUnitaryPoleRegionStatement.{u, v, w}, nonJuxtaposedPoleRegionStatement.{u, v, w}⟩

end Langlands.Global
