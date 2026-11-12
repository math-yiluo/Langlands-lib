import Langlands.Representation.Hecke.NormalQuotientComparison
import Langlands.Representation.Hecke.NormalQuotientAdjunctionProof

/-! # Proof of Renard III.2.10

Renard III.2.10, (III.2.10.1)–(III.2.10.2), Proposition and Corollary,
printed pp.80–82 / PDF pp.86–88.
-/

noncomputable section

open CategoryTheory MeasureTheory MulOpposite

namespace Langlands.Hecke.Homomorphism

universe uP uG v

/-- III.2.10: the Hecke comparison, (III.2.10.1) and both formulas for (III.2.10.2). -/
theorem normalQuotientHeckeStatement : NormalQuotientHeckeStatement.{uP, v} := by
  intro P _ _ _ _ _ _ _ N _ hN _ _ μP _ μM _
  exact ⟨⟨pseudoFIsoF N μP μM⟩, fun K hK p T => rightModule_doubleCoset N μP μM K hK p T,
    coinvariantTensorIso N μP μM,
    fun W w K hK hw => coinvariantTensorIso_hom_mk N μP μM W w K hK hw,
    fun W T w => coinvariantTensorIso_inv_tmul N μP μM W T w⟩

/-- Renard III.2.10: the complete normal-quotient comparison, formulas,
Proposition and Corollary. -/
theorem normalQuotientStatements : NormalQuotientStatements.{uP, uG, v} :=
  ⟨normalQuotientHeckeStatement, normalQuotientAdjunctionStatement,
    normalQuotientInductionAdjunctionStatement⟩

end Langlands.Hecke.Homomorphism
