import Langlands.Global.RankinSelberg.EqualArchimedeanFactorizationReduction
import Langlands.Global.RankinSelberg.RectangleTateProof
import Langlands.Global.RankinSelberg.UnipotentClassProductProof

/-! # The factorization over `S` and the infinite places from the two pointwise premises

Cogdell 2004, proof of Theorem 4.1, pp.219-220. With premise B
(`UnipotentClassProductStatement`) and premise C (`RectangleTateStatement`) proved, the
published combined reduction `ArchimedeanPointwiseFactorizationReductionStatement` leaves only
the two representation-theoretic premises: `ArchimedeanFactorizationStatement` follows from
`UnequalPointwiseFactorizationStatement` and `EqualPointwiseFactorizationStatement`.
See the paired Markdown.
-/

universe u uQ

namespace Langlands.Global.RankinSelbergGlobal

/-- **Conditional factorization.** The unequal-rank and equal-rank pointwise factorization
premises imply `ArchimedeanFactorizationStatement`. -/
def ArchimedeanFactorizationFromPointwiseStatement : Prop :=
  UnequalPointwiseFactorizationStatement.{u, uQ} →
    EqualPointwiseFactorizationStatement.{u, uQ} → ArchimedeanFactorizationStatement.{u, uQ}

/-- Proof of the conditional factorization: the combined reduction applied to the proofs of
premises B and C. -/
theorem archimedeanFactorizationFromPointwise :
    ArchimedeanFactorizationFromPointwiseStatement.{u, uQ} :=
  fun hU hE => archimedeanPointwiseFactorizationReduction hU hE
    UnipotentClass.unipotentClassProductStatement RectangleTate.rectangleTateStatement

end Langlands.Global.RankinSelbergGlobal
