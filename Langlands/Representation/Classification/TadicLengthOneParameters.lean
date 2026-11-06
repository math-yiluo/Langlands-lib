import Langlands.Representation.Classification.SpehLengthOneProof
import Langlands.Representation.Classification.UnitaryElementaryParameters
import Langlands.Representation.Classification.UnitaryParameterRealization

/-! # Actual parameters for length-one Tadic factors

Length-one Speh representations inherit the local block properties of their
discrete-series source. Singleton and complementary factors then have actual
unitary parameter realizations, which assemble by ordered flattening.
-/

noncomputable section

namespace Langlands.Classification

open CategoryTheory GeneralLinear Geometric

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

private theorem blockProperties_rankIso_iff {m n : ℕ} (h : m = n)
    (A : letI := T.topology
      SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear m F.Carrier))
    (B : letI := T.topology
      SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear n F.Carrier))
    (e : letI := T.topology; (h ▸ A) ≅ B) :
    (letI := T.topology;
      Representation.IsIrreducible A.representation ∧
        IsUnitarizable A.representation ∧ T.IsSquareIntegrable A.representation) ↔
    (letI := T.topology;
      Representation.IsIrreducible B.representation ∧
        IsUnitarizable B.representation ∧ T.IsSquareIntegrable B.representation) := by
  cases h
  let := T.topology
  let E := SmoothRep.equivOfIso e
  exact and_congr (Weil.IsomorphismInvariance.irreducible_iff E)
    (and_congr (isUnitarizable_iff_of_equiv E) (T.isSquareIntegrable_iff_of_equiv E))

/-- A supplied length-one Speh representation is itself a unitary
square-integrable block of its actual total rank. -/
theorem blockProperties_lengthOneSpeh (d : SpehDatum.{uF,uV} F T)
    (S : letI := T.topology
      SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear d.degree F.Carrier))
    (hS : d.IsSpeh S) (h1 : d.length = 1) :
    letI := T.topology
    Representation.IsIrreducible S.representation ∧
      IsUnitarizable S.representation ∧ T.IsSquareIntegrable S.representation := by
  let := T.topology
  have h : d.degree = d.rank := by simp [SpehDatum.degree, h1]
  obtain ⟨e⟩ := (spehLengthOneComparison F T d h S h1 hS.1).mp hS
  exact (blockProperties_rankIso_iff F T h S d.delta e).mpr hS.1

/-- Length-one Speh data give an actual singleton parameter realization. -/
def lengthOneSpehParameterRealization (d : SpehDatum.{uF,uV} F T)
    (S : letI := T.topology
      SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear d.degree F.Carrier))
    (hS : d.IsSpeh S) (h1 : d.length = 1) :
    UnitaryParameterRealization F T S := by
  letI := T.topology
  let hr := Nat.mul_pos d.length_pos d.rank_pos
  exact {
    shape := CuspidalSupport.LeviAdmissibility.oneBlock d.degree hr
    blocks := singletonUnitaryBlocks F T hr S
    exponent := fun _ => 0
    valid := isUnitaryGenericDatum_singleton F T hr S
      (blockProperties_lengthOneSpeh F T d S hS h1)
    iso := (singletonUnitaryProductIso F T hr S).symm
  }

/-- A complementary product of a length-one Speh representation has the
actual repeated-pair parameters with the same supplied block at both indices. -/
def lengthOneComplementaryParameterRealization (d : SpehDatum.{uF,uV} F T)
    (S : letI := T.topology
      SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear d.degree F.Carrier))
    (hS : d.IsSpeh S) (h1 : d.length = 1)
    (α : ℝ) (hα0 : 0 < α) (hα : α < (1 / 2 : ℝ)) :
    UnitaryParameterRealization F T (d.complementaryInduced S α) := by
  letI := T.topology
  let hr := Nat.mul_pos d.length_pos d.rank_pos
  exact {
    shape := BlockShape.uniform 2 d.degree hr
    blocks := pairedUnitaryBlocks F T hr S
    exponent := pairedUnitaryExponents α
    valid := isUnitaryGenericDatum_paired F T hr S
      (blockProperties_lengthOneSpeh F T d S hS h1) α hα0 hα
    iso := Iso.refl _
  }

end Langlands.Classification
