import Langlands.BushnellKutzko.SimpleStratumLabelReduction
import Langlands.BushnellKutzko.PureStratumSimpleApproximationProof
import Langlands.BushnellKutzko.MinimalSimpleStratumPolynomialProof

/-! # Labels of simple strata in a principal order: proof (BK94 (1.14))

Proof of `SimpleStratumLabelStatement`, the upper-bound direction of BK94 (1.14) for principal
orders. The induction on the level is `simpleStratumLabel_of`; this module supplies its three
hypotheses: the simple approximation of pure strata (BK93 (2.4.1)(i)),
`pureStratumSimpleApproximation`, and the polynomial labels at depth `n − 1` (BK94 (1.4)–(1.5)),
`minimalSimpleStratumPolynomial`, over the base field and over fields in the universe of `V`.
-/

namespace Langlands.BushnellKutzko

universe uF uV

/-- **BK94 (1.14), printed p. 116, upper-bound direction for principal orders.** The simple
strata `[𝔄,n,m,β]` on a principal lattice chain admit a map to the label set
`P^m_n(e(𝔄), N/e(𝔄); q_F)` such that equal labels give `U(𝔄)`-conjugacy up to equivalence and
each label determines `f(F[β]|F)` and `e(F[β]|F)`. -/
theorem simpleStratumLabel : SimpleStratumLabelStatement.{uF, uV} :=
  simpleStratumLabel_of pureStratumSimpleApproximation minimalSimpleStratumPolynomial
    minimalSimpleStratumPolynomial

end Langlands.BushnellKutzko
