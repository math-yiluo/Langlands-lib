import Langlands.Correspondence.HenniartWeilTameAveraging
import Langlands.Galois.Local.UnramifiedCriterionProof

/-!
# Truncated tame reduction from the fixed-cutoff average
-/

namespace Langlands.Henniart

open Numerical

/-- The pure-rank hypotheses apply to every summand at the original cutoff. -/
theorem weilTameReductionFromAveraging.{uK, uW} :
    WeilTameReductionFromAveragingStatement.{uK, uW} := by
  intro haverage p _ K r m hm hcounts j hj
  obtain ⟨e, he⟩ := haverage p K r m j hm
  have hsummand (i : Fin m) :
      weilConductorCount.{uK, uW} ((e i).1.asPadicField (p := p)) (p ^ r - 1) j =
        (((K.canonicalTopologicalData.residueCardinality - 1) *
          K.canonicalTopologicalData.residueCardinality ^ j : ℕ) : ℕ∞) := by
    let E := (e i).1
    let L := E.asPadicField (p := p)
    let ι := Weil.Local.intermediateEmbedding K E
    have htame : IsTameTotallyRamifiedOfDegree K L ι m := (e i).2
    have hdegree := htame.1
    have hresidue := htame.2.1
    have heL : L.canonicalTopologicalData.ramificationIndex =
        m * K.canonicalTopologicalData.ramificationIndex := by
      simpa only [hdegree, hresidue, Nat.mul_one] using
        PadicField.ramificationIndex_mul_extensionResidueDegree K L ι
    have hqL : L.canonicalTopologicalData.residueCardinality =
        K.canonicalTopologicalData.residueCardinality := by
      simpa only [hresidue, pow_one] using Weil.Local.extensionResidueCardinality K L ι
    have hjL : j < p ^ r * L.canonicalTopologicalData.ramificationIndex := by
      rw [heL, ← Nat.mul_assoc]
      exact hj
    simpa only [hqL] using hcounts r le_rfl L ι m dvd_rfl htame j hjL
  simp only [hsummand, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at he
  have hm0 : m ≠ 0 := fun h => hm (h ▸ dvd_zero p)
  have hcancel := ENat.mul_right_strictMono (a := (m : ℕ∞)) (by exact_mod_cast hm0)
    (ENat.natCast_ne_top m)
  exact hcancel.injective he.symm

end Langlands.Henniart
