import Langlands.Global.RankinSelberg.UnequalEulerFactorizationReduction
import Langlands.Global.RankinSelberg.UnramifiedWhittakerFactorizationProof
import Langlands.Global.RankinSelberg.WhittakerCellDecomposition
import Langlands.Global.RankinSelberg.UnequalUnfoldingProof

/-! # Proof of the unequal-rank partial Euler factorization

`UnequalEulerFactorizationStatement` (Cogdell 2004, §2.2, p.206, with Theorem 3.3, p.215)
follows from the reduction `unequalEulerFactorizationReduction` applied to the published
proofs of its three premises: `UnramifiedWhittaker.unramifiedWhittakerFactorization`
(factorization of global Whittaker functions at an unramified place),
`whittakerCellDecomposition` (one-place cell decomposition of the Whittaker quotient measure)
and `unequalUnfoldingStatement_proof` (unequal-rank unfolding, which supplies the absolute
convergence of the global integral). See the paired Markdown.
-/

universe u uQ
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

/-- **Cogdell 2004, §2.2, p.206, with Theorem 3.3, p.215**: the unequal-rank global Whittaker
integral factors, on a right half-plane uniform in the vectors, as the partial integral over
`S ∪ ∞` times the Euler product of the unramified pair factors outside `S`. -/
theorem unequalEulerFactorization : UnequalEulerFactorizationStatement.{u, uQ} :=
  unequalEulerFactorizationReduction UnramifiedWhittaker.unramifiedWhittakerFactorization
    whittakerCellDecomposition unequalUnfoldingStatement_proof

end Langlands.Global.RankinSelbergGlobal
