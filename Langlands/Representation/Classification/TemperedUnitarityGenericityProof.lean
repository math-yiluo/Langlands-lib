import Langlands.Representation.Classification.SquareIntegrableBlockInductionProof
import Langlands.Representation.Classification.TemperedBlockExhaustionProof
import Langlands.Representation.Classification.SquareIntegrableBlockGenericityProof
import Langlands.Representation.Whittaker.Transport

/-!
# Invariant positive forms and genericity for tempered GL representations

Use analytic tempered exhaustion by square-integrable blocks and transport the
proved unitarity and genericity of their actual normalized product.
-/

namespace Langlands.Classification

universe uF uV

/-- Every irreducible analytically tempered positive-rank GL representation
admits an invariant positive form and is generic for every allowed character. -/
theorem temperedUnitarityAndGenericity
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData) :
    TemperedUnitarityAndGenericity.{uF, uV} F T := by
  let := T.topology
  intro n π hπ ht
  obtain ⟨B, σ, hσ, ⟨i⟩⟩ :=
    temperedBlockExhaustion.{uF, uV} F T (n + 1) (Nat.succ_pos n) π hπ ht
  let e := SmoothRep.equivOfIso i
  refine ⟨(isUnitarizable_iff_of_equiv e).mpr
    (squareIntegrableBlockInduction.{uF, uV} F T
      (n + 1) (Nat.succ_pos n) B σ hσ).2.1, ?_⟩
  intro ψ
  exact (Whittaker.isGeneric_iff_of_equiv ψ n e).mpr
    (squareIntegrableBlockGenericity.{uF, uV} F T n B σ hσ ψ)

end Langlands.Classification
