import Langlands.Representation.Classification.IsobaricSum
import Langlands.Representation.Classification.MultisegmentHeadExhaustionProof
import Langlands.Representation.Classification.MultisegmentHeadExistenceProof

/-! Existence of local isobaric sums by pooling the multisegments of the factors. -/

namespace Langlands.PadicField.TopologicalData

open Classification

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

private theorem degree_sum {k : ℕ} (a : Fin k → T.Multisegment.{max uF uV, uF}) :
    (∑ i, a i).degree = ∑ i, (a i).degree :=
  map_sum (Multiset.sumAddMonoidHom.comp (Multiset.mapAddMonoidHom Segment.degree)) a Finset.univ

/-- A finite family of irreducible smooth representations has an isobaric
sum on the general linear group whose rank is the sum of the input ranks. -/
theorem exists_isIsobaricSum {k N : ℕ} {n : Fin k → ℕ} (hn : ∑ i, n i = N)
    (π : letI := T.topology
      ∀ i, SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (n i) F.Carrier))
    (hπ : letI := T.topology; ∀ i, (π i).representation.IsIrreducible) :
    letI := T.topology
    ∃ A : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear N F.Carrier),
      T.IsIsobaricSum.{max uF uV, uF} π A := by
  let := T.topology
  choose a ha hhead using fun i => multisegmentHeadExhaustion.{uF, uV} F T (n i) (π i) (hπ i)
  have hdegree : (∑ i, a i).degree = N := by
    rw [degree_sum]
    exact (Finset.sum_congr rfl fun i _ => ha i).trans hn
  rw [← hdegree]
  obtain ⟨A, hA⟩ := multisegmentHeadExistence.{uF, uV} F T (∑ i, a i)
  exact ⟨A, a, hhead, hA⟩

end Langlands.PadicField.TopologicalData
