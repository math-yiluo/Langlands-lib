import Langlands.Representation.CuspidalSupport.AllRankBinaryCuspidalConcatenation
import Langlands.Representation.Induction.BinaryProductSubquotients
import Langlands.Representation.Filtration.SubquotientAlgebraProof

/-! Actual cuspidal presentations and support addition for binary products. -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace Langlands.PadicField.TopologicalData

open GeneralLinear

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  {T : F.TopologicalData}

namespace BinaryCuspidalSupport

/-- An actual presentation of a binary product inside the cuspidal induction
of the concatenated supplied families, in the original datum universe. -/
structure ProductOccurrenceData {k l a b : ℕ}
    (ρ : Fin k → CuspidalDatum.{uV, uF} T)
    (τ : Fin l → CuspidalDatum.{uV, uF} T)
    (hρ : ∑ i, (ρ i).rank = a) (hτ : ∑ i, (τ i).rank = b)
    (A : letI := T.topology
      ∀ i, SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := (ρ i).rank))
    (C : letI := T.topology
      ∀ i, SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := (τ i).rank))
    (X : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear a F.Carrier))
    (Y : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear b F.Carrier)) where
  concatenation : BinaryCuspidalConcatenation.AllRankData ρ τ hρ hτ A C
  subspace : letI := T.topology
    Subrepresentation (T.cuspidalProductInduced concatenation.family
      concatenation.rank_sum concatenation.representatives).representation
  kernel : letI := T.topology
    Subrepresentation (SmoothRep.subrepresentation
      (T.cuspidalProductInduced concatenation.family
        concatenation.rank_sum concatenation.representatives) subspace).representation
  occurrenceIso : letI := T.topology
    (T.binaryNormalizedProductFunctor a b).obj (X, Y) ≅
      SmoothRep.subquotient
        (T.cuspidalProductInduced concatenation.family
          concatenation.rank_sum concatenation.representatives) subspace kernel

/-- Combine two actual occurrences in supplied cuspidal inductions into an
actual occurrence of their product in the concatenated cuspidal induction. -/
def productOccurrenceData {k l a b : ℕ}
    (ρ : Fin k → CuspidalDatum.{uV, uF} T)
    (τ : Fin l → CuspidalDatum.{uV, uF} T)
    (hρ : ∑ i, (ρ i).rank = a) (hτ : ∑ i, (τ i).rank = b)
    (A : letI := T.topology
      ∀ i, SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := (ρ i).rank))
    (C : letI := T.topology
      ∀ i, SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := (τ i).rank))
    (X : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear a F.Carrier))
    (Y : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear b F.Carrier))
    (hX : letI := T.topology
      SmoothRep.IsSubquotient X (T.cuspidalProductInduced ρ hρ A))
    (hY : letI := T.topology
      SmoothRep.IsSubquotient Y (T.cuspidalProductInduced τ hτ C)) :
    ProductOccurrenceData ρ τ hρ hτ A C X Y := by
  let := T.topology
  let c := BinaryCuspidalConcatenation.allRank ρ τ hρ hτ A C
  have hproduct := T.binaryProduct_isSubquotient hX hY
  have hflat := hproduct.of_iso_right c.productIso.symm
  let S := Classical.choose hflat
  let K := Classical.choose (Classical.choose_spec hflat)
  let e := Classical.choice (Classical.choose_spec (Classical.choose_spec hflat))
  exact ⟨c, S, K, e⟩

end BinaryCuspidalSupport

/-- Each irreducible actual subquotient of a binary product has the sum of
any two supplied supports as a supercuspidal support. -/
theorem binaryProductConstituentSupport {a b : ℕ}
    {X : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear a F.Carrier)}
    {Y : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear b F.Carrier)}
    {D : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (a + b) F.Carrier)}
    {s t : Multiset (CuspidalDatum.{uV, uF} T)}
    (hX : T.IsSupercuspidalSupport X s)
    (hY : T.IsSupercuspidalSupport Y t)
    (hD : letI := T.topology; D.IsIrreducible)
    (hDP : letI := T.topology
      SmoothRep.IsSubquotient D ((T.binaryNormalizedProductFunctor a b).obj (X, Y))) :
    T.IsSupercuspidalSupport D (s + t) := by
  let := T.topology
  obtain ⟨k, ρ, hρs, hρ, A, hA, _, hXP⟩ := hX
  obtain ⟨l, τ, hτt, hτ, C, hC, _, hYQ⟩ := hY
  let d := BinaryCuspidalSupport.productOccurrenceData ρ τ hρ hτ A C X Y hXP hYQ
  let c := d.concatenation
  refine ⟨c.count, c.family, ?_, c.rank_sum, c.representatives,
    c.represents hA hC, hD, ?_⟩
  · rw [c.multiset_eq, hρs, hτt]
  · exact smoothSubquotientTransitivity ℂ _
      (T.cuspidalProductInduced c.family c.rank_sum c.representatives)
      ((T.binaryNormalizedProductFunctor a b).obj (X, Y)) D
      hDP ⟨d.subspace, d.kernel, ⟨d.occurrenceIso⟩⟩

end Langlands.PadicField.TopologicalData
