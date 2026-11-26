import Langlands.Global.AdelicEisensteinConvergenceProof
import Langlands.Global.EisensteinConstantTerm.Reduction
import Langlands.Global.EisensteinConstantTerm.GeometricLemmaUnfoldingProof

/-! # The constant-term formula for adelic Eisenstein series (proof)

Bernstein–Lapid Lemma 6.10 (6.17) and Mœglin–Waldspurger II.1.7: the constant term along `Q` of
the Eisenstein series of `φ` is the sum over the double cosets `Q(F) w P(F)` of the intertwining
integrals of the constant terms of `φ` along `P'_w`. The reduction
`eisensteinConstantTerm_of_convergence_of_unfolding` derives the formula from the absolute
convergence of Eisenstein series (`eisensteinAbsoluteConvergence`) and the integration identity
of the geometric lemma (`geometricLemmaUnfolding`). -/

universe u

namespace Langlands.Global

/-- **The constant-term formula** for adelic Eisenstein series (Bernstein–Lapid Lemma 6.10
(6.17), Mœglin–Waldspurger II.1.7). -/
theorem eisensteinConstantTerm : EisensteinConstantTermStatement.{u} :=
  eisensteinConstantTerm_of_convergence_of_unfolding eisensteinAbsoluteConvergence
    geometricLemmaUnfolding

end Langlands.Global
