import Langlands.Global.RankinSelberg.ComplexOrdinaryNormalizedAllGrowth

/-!
# Entire normalizations of the ordinary complex Rankin–Selberg integrals

A proof of `Langlands.Global.RankinSelbergGlobal.ComplexOrdinaryNormalizedContinuationStatement`:
the first component of the Library theorem `complexOrdinaryNormalizedAllGrowth`, which proves the
conjunction of this statement and the strip growth of the normalizations. See the paired
Markdown.
-/

namespace Langlands.Global.RankinSelbergGlobal

/-- **Continuation of the ordinary complex integrals (Jacquet 2009, Theorem 2.1(ii)).** In every
unequal and equal rank, every ordinary complex pair integral on the Library's Whittaker models
has an entire normalization by the pair `L`-factor `complexPairLFactor d e`. -/
theorem complexOrdinaryNormalizedContinuation : ComplexOrdinaryNormalizedContinuationStatement :=
  complexOrdinaryNormalizedAllGrowth.1

end Langlands.Global.RankinSelbergGlobal
