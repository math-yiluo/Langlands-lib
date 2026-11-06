import Langlands.Representation.Classification.TadicUnitaryStatement
import Langlands.Representation.Classification.LeviDiscreteSeriesTemperedProof
import Langlands.Representation.Classification.CanonicalConstituents

/-!
# Centered Speh induction as a tempered Langlands standard module

The actual centered product is definitionally the standard module of a
strictly decreasing tempered Langlands datum. A strong irreducible head of
this module supplies the quotient and uniqueness clauses of the Speh relation.
-/

noncomputable section

namespace Langlands.Classification

open CategoryTheory GeneralLinear

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} {T : F.TopologicalData}

namespace SpehDatum

variable (d : SpehDatum.{uF, uV} F T)

theorem degree_pos : 0 < d.degree :=
  Nat.mul_pos d.length_pos d.rank_pos

/-- The real centered exponents decrease strictly in the original order. -/
theorem exponent_strictAnti : StrictAnti d.exponent := by
  intro i j hij
  dsimp only [exponent]
  exact sub_lt_sub_left (by exact_mod_cast hij) _

/-- The same constant family of discrete-series blocks and centered exponents,
now packaged as actual tempered Langlands data. -/
def temperedLanglandsDatum (hd : d.IsDiscreteSeries) :
    T.TemperedLanglandsDatum.{max uF uV, uF} d.degree := by
  let := T.topology
  refine
    { shape := BlockShape.uniform d.length d.rank d.rank_pos
      blocks := fun _ => d.delta
      irreducible := fun _ => hd.1
      tempered := fun _ => ?_
      exponent := d.exponent
      strictAnti := d.exponent_strictAnti }
  change T.IsTempered d.delta.representation
  have := T.generalLinearTopologicalGroup d.rank
  let := T.centralQuotientMeasurableSpace d.rank
  have := T.centralQuotientBorelSpace d.rank
  intro μ _
  exact isTemperedModCenter_of_squareIntegrable μ (hd.2.2 μ)

@[simp]
theorem temperedLanglandsDatum_standardModule (hd : d.IsDiscreteSeries) :
    (d.temperedLanglandsDatum hd).standardModule = d.centeredInduced :=
  rfl

/-- The tempered Langlands quotient relation is exactly the actual quotient
relation used in the definition of a Speh representation. -/
theorem isLanglandsQuotient_iff (hd : d.IsDiscreteSeries)
    (π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear d.degree F.Carrier)) :
    letI := T.topology
    (d.temperedLanglandsDatum hd).IsLanglandsQuotient π ↔
      IsIrreducibleQuotient d.centeredInduced.representation π.representation :=
  Iff.rfl

/-- A strong Langlands head of the centered standard module is a Speh
representation: the common kernel identifies every irreducible quotient. -/
theorem isSpeh_of_isLanglandsHead (hd : d.IsDiscreteSeries)
    {π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear d.degree F.Carrier)}
    (hπ : (d.temperedLanglandsDatum hd).IsLanglandsHead π) :
    d.IsSpeh π := by
  let := T.topology
  have hhead : IsIrreducibleHead d.centeredInduced.representation π.representation := hπ
  have hquot : IsIrreducibleQuotient d.centeredInduced.representation π.representation := by
    obtain ⟨hπi, q, hq, -⟩ := id hhead
    exact ⟨hπi, q, hq⟩
  refine ⟨hd, hquot, ?_⟩
  intro π' hπ'
  obtain ⟨hπi, q, hq, -⟩ := id hhead
  obtain ⟨hπi', q', hq'⟩ := hπ'
  exact ⟨SmoothRep.mkIso
    ((headEquivOfSurjective q' hq' (hhead.headKernel_eq _ hπi' q' hq')).symm.trans
      (headEquivOfSurjective q hq (hhead.headKernel_eq _ hπi q hq)))⟩

end SpehDatum

end Langlands.Classification
