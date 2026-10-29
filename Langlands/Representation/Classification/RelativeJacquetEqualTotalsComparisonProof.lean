import Langlands.Representation.Classification.RelativeJacquetEqualTotalsComparisonStatement
import Langlands.Representation.Classification.RelativeJacquetFiltrationMultiplicityProof
import Langlands.Representation.Classification.RelativeJacquetEmbeddingProof
import Langlands.Representation.Filtration.SimpleSubquotientFactorProof
import Langlands.Representation.Filtration.MultiplicityIndependenceProof
import Langlands.Representation.Filtration.MultiplicityTransportProof
import Langlands.Representation.Parabolic.RefinedOppositeJacquetTensor
import Langlands.Representation.Induction.Equivalences
import Mathlib.Algebra.Order.BigOperators.Group.Finset

noncomputable section

open scoped BigOperators

namespace Langlands

open GeneralLinear Geometric RelativeJacquetMultiplicity
  RelativeJacquetFiltrationMultiplicityProof

universe uF uV uW uX

/-- Decompose the actual totals, compare every grade, and transport the selected
simple subquotient's common count through actual Jacquet equivalences. -/
theorem glRelativeJacquetEqualTotalsComparison :
    GLRelativeJacquetEqualTotalsComparisonStatement.{uF, uV, uW, uX} := by
  classical
  intro p hp F T
  let := T.topology
  intro n hn B S A hA l s hs had τ N hin hout μ hμi hμa hsub
  let := T.leviTopologicalGroup B
  let := T.generalLinearTopologicalGroup n
  obtain ⟨a, ha, hasum⟩ :=
    ((glRelativeJacquetFiltrationMultiplicity.{uF, uV, uW} p F T n B S).1
      A hA l s τ N).mp hin
  obtain ⟨b, hb, hbsum⟩ :=
    ((glRelativeJacquetFiltrationMultiplicity.{uF, uV, uW} p F T n B S).2
      A hA l s τ N).mp hout
  have hle : ∀ i : Fin l, a i ≤ b i := by
    intro i
    obtain ⟨m, hm, hmi⟩ :=
      (glRelativeJacquetEmbedding.{uF, uW, uV} p F T n hn B S
        (s.gradedRepresentation i) (hs i) (had i)).2 τ (b i) (hb i)
    rw [hm.unique (ha i)] at hmi
    exact hmi
  have heq : ∀ i : Fin l, a i = b i := by
    intro i
    exact (Finset.sum_eq_sum_iff_of_le (fun i _ => hle i)).mp
      (hasum.trans hbsum.symm) i (Finset.mem_univ i)
  obtain ⟨U, q, hq⟩ := hsub
  let Aₛ : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier) := SmoothRep.of A.ρ hA
  let D : SmoothRep.{0, uF, uX} ℂ (B.Levi F.Carrier) := SmoothRep.of μ.ρ hμa.1
  let e : (SmoothRep.subquotient Aₛ U q.ker).representation.Equiv D.representation :=
    Representation.Equiv.mk (q.toLinearMap.quotKerEquivOfSurjective hq) fun g => by
      apply Submodule.linearMap_qext
      ext v
      exact Representation.IntertwiningMap.isIntertwining _ _ q g v
  obtain ⟨j, ⟨eμ⟩⟩ :=
    simpleSubquotientFactor ℂ (B.Levi F.Carrier) Aₛ l s hs D U q.ker hμi ⟨e.symm⟩
  let Ei := RefinedOppositeJacquetTensor.normalizedRefinedOppositeJacquetCongr T B S eμ
  let Eo := composedOppositeJacquetCongr T B S (T.normalizedParabolicInducedEquiv B eμ)
  refine ⟨a j, ?_, ?_⟩
  · exact (equivJordanHolderMultiplicityTransport ℂ (refinedLevi F.Carrier B S)
      (innerJacquet T B S μ) (innerJacquet T B S (s.gradedRepresentation j))
      τ τ Ei (Representation.Equiv.refl _) (a j)).mpr (ha j)
  · have hbj : HasJordanHolderMultiplicity
        (ambientJacquet T B S (s.gradedRepresentation j)) τ (a j) := by
      rw [heq j]
      exact hb j
    exact (equivJordanHolderMultiplicityTransport ℂ (refinedLevi F.Carrier B S)
      (ambientJacquet T B S μ) (ambientJacquet T B S (s.gradedRepresentation j))
      τ τ Eo (Representation.Equiv.refl _) (a j)).mpr hbj

end Langlands
