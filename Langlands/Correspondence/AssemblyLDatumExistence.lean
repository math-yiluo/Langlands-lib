import Langlands.Combinatorics.FiniteOccurrenceMatching
import Langlands.Correspondence.AssemblyLTwistedSupercuspidal
import Langlands.Representation.Classification.SegmentUniverseLift
import Langlands.Representation.Classification.OrderedSegmentSquareIntegrableConversionProof
import Langlands.Representation.Smooth.SmallRealizationProof

/-!
# Square-integrable data of multisegment heads

Every precedence-ordered multisegment Langlands head has a square-integrable
Langlands datum with blocks in the carrier universe `uA` whose blocks are, up to a
permutation, models of the segment heads. This proves the premise
`MultisegmentHeadDatumExistence` of `AssemblyLReduction` without new hypotheses,
and removes it from the reduction of `AssemblyLInheritanceStatement`.
-/

noncomputable section

namespace Langlands.Correspondence

universe uF uP uA

open CategoryTheory PadicField.TopologicalData

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance assemblyLDatumFieldTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology

local instance assemblyLDatumGeneralLinearTopology (n : ℕ) :
    TopologicalSpace (GeneralLinear n F.Carrier) :=
  F.canonicalGeneralLinearTopology n

/-- The ordered segment conversion of the Library, extended to rank `0`, where the
datum has no segments. -/
theorem orderedSegmentSquareIntegrableConversion_of_rank {n : ℕ}
    (d : SegmentProductDatum.{max uF uA, uF} F.canonicalTopologicalData n)
    (ho : d.IsPrecedenceOrdered) (hh : d.HasSegmentHeads) :
    ∃ e : SquareIntegrableLanglandsDatum.{max uF uA, uF} F.canonicalTopologicalData n,
      Nonempty (d.induced ≅ e.induced) ∧
        ∃ σ : Fin d.length ≃ Fin e.shape.length,
          ∀ i, ∃ h : (d.segments i).degree = e.shape.size (σ i),
            Nonempty ((h ▸ d.blocks i) ≅ e.blocks (σ i)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hfalse : ∀ i : Fin d.length, False := fun i => by
      have h1 := Finset.single_le_sum (f := fun j => (d.segments j).degree)
        (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
      rw [d.degree_sum] at h1
      exact absurd h1 (Nat.not_le.mpr (d.segments i).degree_pos)
    refine ⟨{ shape := d.shape
              blocks := d.blocks
              irreducible := fun i => (hfalse i).elim
              essentiallySquareIntegrable := fun i => (hfalse i).elim
              unitaryExponent := fun i => (hfalse i).elim
              antitone := fun i _ _ => (hfalse i).elim },
      ⟨Iso.refl _⟩, Equiv.refl _, fun i => (hfalse i).elim⟩
  · exact Classification.orderedSegmentSquareIntegrableConversion.{uF, uA} F
      F.canonicalTopologicalData n hn d ho hh

/-- Each block of a square-integrable datum has an irreducible realization with
carrier in `uA`. -/
theorem exists_smallBlock {n : ℕ}
    (e : SquareIntegrableLanglandsDatum.{max uF uA, uF} F.canonicalTopologicalData n)
    (i : Fin e.shape.length) :
    ∃ Q : SmoothRep.{0, uF, uA} ℂ (GeneralLinear (e.shape.size i) F.Carrier),
      Q.IsIrreducible ∧ Nonempty ((e.blocks i).representation.Equiv Q.representation) :=
  padicIrreducibleSmoothSmallRealization.{uF, max uF uA, uA} p F F.canonicalTopologicalData _
    (e.blocks i) (e.irreducible i)

/-- The square-integrable datum with the same shape and exponents whose blocks are
the chosen realizations of `exists_smallBlock`. -/
def smallDatum {n : ℕ}
    (e : SquareIntegrableLanglandsDatum.{max uF uA, uF} F.canonicalTopologicalData n) :
    SquareIntegrableLanglandsDatum.{uA, uF} F.canonicalTopologicalData n where
  shape := e.shape
  blocks i := (exists_smallBlock.{uF, uA} F e i).choose
  irreducible i := (exists_smallBlock.{uF, uA} F e i).choose_spec.1
  essentiallySquareIntegrable i :=
    (isEssentiallySquareIntegrable_iff_of_equiv
      (exists_smallBlock.{uF, uA} F e i).choose_spec.2.some).mp (e.essentiallySquareIntegrable i)
  unitaryExponent i :=
    (e.unitaryExponent i).ofEquiv (exists_smallBlock.{uF, uA} F e i).choose_spec.2.some
  antitone := e.antitone

/-- The block equivalences of `smallDatum`. -/
def smallBlockEquiv {n : ℕ}
    (e : SquareIntegrableLanglandsDatum.{max uF uA, uF} F.canonicalTopologicalData n)
    (i : Fin e.shape.length) :
    ((smallDatum.{uF, uA} F e).blocks i).representation.Equiv (e.blocks i).representation :=
  (exists_smallBlock.{uF, uA} F e i).choose_spec.2.some.symm

/-- The induced representations of `smallDatum e` and `e` are equivalent. -/
def smallDatumInducedEquiv {n : ℕ}
    (e : SquareIntegrableLanglandsDatum.{max uF uA, uF} F.canonicalTopologicalData n) :
    (smallDatum.{uF, uA} F e).induced.representation.Equiv e.induced.representation :=
  normalizedProductInducedEquiv.{uF, uA, max uF uA} F.canonicalTopologicalData e.shape
    (smallBlockEquiv.{uF, uA} F e)

/-- A `uA`-realization of a representation isomorphic, after rank transport, to a
segment head is a segment-head model. -/
theorem isSegmentHeadModel_of_iso {Δ : Segment.{uA, uF} F.canonicalTopologicalData} {m : ℕ}
    (P : SmoothRep.{0, uF, max uF uA} ℂ (GeneralLinear Δ.degree F.Carrier))
    (hP : F.canonicalTopologicalData.IsSegmentHead Δ P)
    (B : SmoothRep.{0, uF, max uF uA} ℂ (GeneralLinear m F.Carrier))
    (Q : SmoothRep.{0, uF, uA} ℂ (GeneralLinear m F.Carrier))
    (eQ : Q.representation.Equiv B.representation)
    (h : Δ.degree = m) (iso : (h ▸ P) ≅ B) :
    IsSegmentHeadModel F Δ Q := by
  subst h
  exact ⟨rfl, P, hP, ⟨eQ.trans (SmoothRep.equivOfIso iso).symm⟩⟩

/-- Multisegment Langlands heads have square-integrable data with blocks in `uA`
that are segment-head models of the segments, up to a permutation. -/
theorem multisegmentHeadDatumExistence : MultisegmentHeadDatumExistence.{uF, uA} F := by
  intro r Δ n J hJ
  obtain ⟨d, hdm, hdJ⟩ := hJ
  obtain ⟨τ, hτ⟩ := Langlands.Combinatorics.exists_equiv_of_ofFn_multiset_eq d.segments Δ hdm
  have hd'J := (d.universeLift_isLanglandsHead_iff J).mpr hdJ
  obtain ⟨e, ⟨iso⟩, σ, hσ⟩ :=
    orderedSegmentSquareIntegrableConversion_of_rank.{uF, uA} F d.universeLift hd'J.1 hd'J.2.1
  refine ⟨smallDatum.{uF, uA} F e, ?_, σ.symm.trans τ, fun k => ?_⟩
  · have hq : Classification.IsIrreducibleQuotient d.universeLift.induced.representation
        J.representation := by
      obtain ⟨hπ, q, hq, -⟩ := hd'J.2.2
      exact ⟨hπ, q, hq⟩
    exact (hq.of_equiv (SmoothRep.equivOfIso iso)).of_equiv (smallDatumInducedEquiv.{uF, uA} F e).symm
  · obtain ⟨i, rfl⟩ := σ.surjective k
    obtain ⟨h, ⟨iso_i⟩⟩ := hσ i
    have hm := isSegmentHeadModel_of_iso F (Δ := d.segments i) (d.blocks i) (hdJ.2.1 i) (e.blocks (σ i))
      ((smallDatum.{uF, uA} F e).blocks (σ i)) (smallBlockEquiv.{uF, uA} F e (σ i)) h iso_i
    have hk : (σ.symm.trans τ) (σ i) = τ i := congrArg τ (σ.symm_apply_apply i)
    exact (congrArg (fun D => IsSegmentHeadModel F D ((smallDatum.{uF, uA} F e).blocks (σ i)))
      ((congrArg Δ hk).trans (hτ i).symm)).mpr hm

/-- Pair L-factor inheritance of the assembled correspondence follows from JPSS (9.5)
for square-integrable data, Henniart's segment-head L formula and the two
parameter-side premises on arithmetic pair L-factors. -/
theorem assemblyLInheritance_of_rankinSelberg_of_blockPairs
    (hJ : RankinSelberg.SquareIntegrableDataLFactorStatement.{uF, uA, uA})
    (hD : ArithmeticPairLDirectSum.{uF, uP} F)
    (hH : RankinSelberg.SegmentHeadLFactorStatement.{uF, uA, uA})
    (hB : ArithmeticBlockPairLFactor.{uF, uP} F) :
    AssemblyLInheritanceStatement.{uF, uP, uA} F :=
  assemblyLInheritance_of_segmentHeads_of_blockPairs F
    (multisegmentHeadDatumExistence.{uF, uA} F) hJ hD hH hB

end Langlands.Correspondence
