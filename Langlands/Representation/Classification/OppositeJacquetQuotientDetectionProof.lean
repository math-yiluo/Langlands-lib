import Langlands.Representation.Classification.OppositeJacquetQuotientDetectionStatement
import Langlands.Representation.Classification.CuspidalJacquetFunctors
import Langlands.Representation.Jacquet.ExactProof
import Langlands.Representation.Parabolic.SecondAdjointnessProof
import Langlands.Representation.Filtration.SimpleMapMultiplicityDetectionProof

/-! Positive opposite-Jacquet multiplicity for admissible quotients of induction. -/

namespace Langlands

open CuspidalJacquetMultiplicity Representation

universe uF uV uW

/-- Actual second adjointness detects the inducing type in the opposite
Jacquet module of a quotient; the ambient series bounds its positive count. -/
theorem oppositeJacquetQuotientDetection :
    OppositeJacquetQuotientDetectionStatement.{uF, uV, uW} := by
  intro p hp F T
  let := T.topology
  intro n hn B σ hσ hσadm P hPadm q hq hq0 M hM
  obtain ⟨E, -, -⟩ :=
    Parabolic.normalizedSecondAdjointness.{uF, uV, uW}.1 p F T n hn B
  have hnonzero : E σ P hσadm hPadm q ≠ 0 := by
    intro hz
    apply hq0
    exact (E σ P hσadm hPadm).injective (hz.trans (map_zero _).symm)
  have hsurj : Function.Surjective (oppositeMap T B q) :=
    coinvariants_map_surjective
      (Jacquet.restrictMap q (B.oppositeUnipotentSubgroup F.Carrier)) hq
  exact jordanHolderQuotientSimpleMapDetection ℂ (B.Levi F.Carrier)
    (oppositeJacquet T B (induced T B σ)) (oppositeJacquet T B P) σ hσ
    (oppositeMap T B q) hsurj M hM (Or.inl ⟨_, hnonzero⟩)

end Langlands
