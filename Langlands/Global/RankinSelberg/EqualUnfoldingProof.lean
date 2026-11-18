import Langlands.Global.RankinSelberg.EqualUnfoldingReduction
import Langlands.Global.RankinSelberg.EqualUnfoldingGauge
import Langlands.Global.RankinSelberg.CuspidalWhittakerExpansionProof
import Langlands.Global.RankinSelberg.DualWhittakerExpansionProof

/-! # Proof of the ordinary and dual unfolding for equal-rank cuspidal pairs

This module proves `EqualUnfoldingStatement` (Cogdell 2004, §2.3). It applies the conditional
reduction `equalUnfoldingReduction` to the published proofs of its four premises: the
Whittaker expansions E and Ẽ (`cuspidalWhittakerExpansionStatement_proof`,
`dualCuspidalWhittakerExpansionStatement_proof`) and the gauge integrability premises G and G̃
(`equalUnfoldingGauge`).
-/

universe u
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

/-- The gauge premises G and G̃ for all equal-rank pairs imply `EqualUnfoldingStatement`: the
Whittaker-expansion premises E and Ẽ of `equalUnfoldingReduction` are proved in the Library. -/
theorem equalUnfoldingStatement_of_gauge (hG : EqualUnfoldingGaugeStatement.{u}) :
    EqualUnfoldingStatement.{u} :=
  equalUnfoldingReduction fun F _ _ _ r T T' =>
    ⟨cuspidalWhittakerExpansionStatement_proof F r T,
      dualCuspidalWhittakerExpansionStatement_proof F r T, hG.1 F r T T', hG.2 F r T T'⟩

/-- The ordinary and dual unfolding for every pair of actual cuspidal realizations of `GL_n`
over every number field `F : Type u` whose additive adelic quotient is compact. -/
theorem equalUnfoldingStatement_proof : EqualUnfoldingStatement.{u} :=
  equalUnfoldingStatement_of_gauge equalUnfoldingGauge.{u}

end Langlands.Global.RankinSelbergGlobal
