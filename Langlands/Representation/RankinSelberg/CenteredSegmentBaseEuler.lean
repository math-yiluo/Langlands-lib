import Langlands.Representation.Classification.CenteredUnitarySegmentFamily
import Langlands.Representation.Classification.SingletonSegmentSocle
import Langlands.Representation.RankinSelberg.UnitarySupercuspidalBaseFamily

/-! # Actual Euler factors of the centered bases of segment parameters -/

noncomputable section

namespace Langlands.Classification

open CategoryTheory GeneralLinear

universe uF uV uI

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

private theorem supercuspidal_castRank {r s : ℕ} (h : r = s)
    (A : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear r F.Carrier))
    (hs : letI := T.topology; IsSupercuspidal A.representation) :
    letI := T.topology; IsSupercuspidal (T.castRank h A).representation := by
  cases h
  exact hs

private theorem unitarizable_castRank {r s : ℕ} (h : r = s)
    (A : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear r F.Carrier))
    (hu : letI := T.topology; IsUnitarizable A.representation) :
    letI := T.topology; IsUnitarizable (T.castRank h A).representation := by
  cases h
  exact hu

private def equiv_castRank {r s : ℕ} (h : r = s)
    (A A' : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear r F.Carrier))
    (e : letI := T.topology; A.representation.Equiv A'.representation) :
    letI := T.topology
    (T.castRank h A).representation.Equiv (T.castRank h A').representation := by
  cases h
  exact e

private def castAction {r s : ℕ} (h : r = s)
    {V : Type (max uF uV)} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V) :
    Representation ℂ (GeneralLinear (s + 1) F.Carrier) V :=
  h ▸ ρ

namespace SquareIntegrableSegmentParameter

variable {n m : ℕ}
  {π : letI := T.topology
    SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)}
  {σ : letI := T.topology
    SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear m F.Carrier)}

/-- Keep the chosen actual midpoint base, expressing its positive rank as a
successor for the pair-factor interface. -/
def positiveBase (d : SquareIntegrableSegmentParameter F T n π) :
    letI := T.topology
    SmoothRep.{0, uF, max uF uV} ℂ
      (GeneralLinear (d.segment.rank - 1 + 1) F.Carrier) :=
  T.castRank (Nat.sub_add_cancel (Nat.succ_le_of_lt d.segment.rank_pos)).symm d.base.obj

theorem positiveBase_isIrreducible (d : SquareIntegrableSegmentParameter F T n π) :
    letI := T.topology; (d.positiveBase F T).IsIrreducible :=
  T.isIrreducible_castRank _ d.base.obj d.base.property.1

theorem positiveBase_isSupercuspidal (d : SquareIntegrableSegmentParameter F T n π) :
    letI := T.topology; IsSupercuspidal (d.positiveBase F T).representation :=
  supercuspidal_castRank F T _ d.base.obj d.base.property.2

theorem positiveBase_isUnitarizable (d : SquareIntegrableSegmentParameter F T n π) :
    letI := T.topology; IsUnitarizable (d.positiveBase F T).representation :=
  unitarizable_castRank F T _ d.base.obj d.unitarizable

private theorem midpointBases_equiv
    (Δ Δ' : T.Segment.{max uF uV, uF}) (h : Δ = Δ')
    (A : letI := T.topology
      SupercuspidalRep.{uF, max uF uV} (F := F.Carrier) (n := Δ.rank))
    (A' : letI := T.topology
      SupercuspidalRep.{uF, max uF uV} (F := F.Carrier) (n := Δ'.rank))
    (hA : (Δ.twist (((Δ.length : ℝ) - 1) / 2)).base.IsRepresentedBy A)
    (hA' : (Δ'.twist (((Δ'.length : ℝ) - 1) / 2)).base.IsRepresentedBy A') :
    letI := T.topology
    Nonempty ((castAction F (congrArg (fun D : T.Segment.{max uF uV, uF} => D.rank - 1) h)
      (T.castRank (Nat.sub_add_cancel (Nat.succ_le_of_lt Δ.rank_pos)).symm
        A.obj).representation).Equiv
      (T.castRank (Nat.sub_add_cancel (Nat.succ_le_of_lt Δ'.rank_pos)).symm
        A'.obj).representation) := by
  let := T.topology
  cases h
  obtain ⟨e⟩ := (SupercuspidalRep.isoClass_eq_iff A A').mp (hA.trans hA'.symm)
  exact ⟨equiv_castRank F T _ A.obj A'.obj
    (SmoothRep.equivOfIso ((supercuspidalProperty (F := F.Carrier)
      (n := Δ.rank)).ι.mapIso e))⟩

/-- Equal original segments identify the actual chosen midpoint bases after
the same original-rank transports, independently of their choices. -/
theorem positiveBase_equiv_of_segment_eq
    (d : SquareIntegrableSegmentParameter F T n π)
    (d' : SquareIntegrableSegmentParameter F T m σ) (h : d.segment = d'.segment) :
    letI := T.topology
    Nonempty ((castAction F (congrArg (fun D : T.Segment.{max uF uV, uF} => D.rank - 1) h)
      (d.positiveBase F T).representation).Equiv (d'.positiveBase F T).representation) :=
  midpointBases_equiv F T d.segment d'.segment h d.base d'.base d.base_repr d'.base_repr

end SquareIntegrableSegmentParameter

end Langlands.Classification

namespace Langlands.RankinSelberg

open GeneralLinear Classification HarmonicAnalysis Whittaker

universe uF uV uI

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}

/-- Certified Euler data for each chosen centered base paired with the actual
smooth dual of another base. -/
def centeredSegmentBaseEulerFamily
    (hEq : SupercuspidalEqualRankLFactorStatement.{uF, max uF uV, max uF uV})
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
    {I : Type uI} {n : I → ℕ}
    {δ : letI := F.canonicalTopologicalData.topology
      ∀ i, SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (n i) F.Carrier)}
    (d : ∀ i, SquareIntegrableSegmentParameter F F.canonicalTopologicalData (n i) (δ i)) :
    letI := F.canonicalTopologicalData.topology
    ∀ i j, letI := F.canonicalTopologicalData.generalLinearTopologicalGroup ((d j).segment.rank - 1 + 1)
      SupercuspidalPairEuler ψ ν ((d i).positiveBase F F.canonicalTopologicalData).representation
        (smoothContragredient ((d j).positiveBase F F.canonicalTopologicalData).representation) := by
  let := F.canonicalTopologicalData.topology
  exact unitarySupercuspidalBaseFamily hEq ψ ν (fun i => (d i).segment.rank - 1)
    (fun i => (d i).positiveBase F F.canonicalTopologicalData)
    (fun i => ((d i).positiveBase F F.canonicalTopologicalData).representation)
    (fun i => (d i).positiveBase_isIrreducible F F.canonicalTopologicalData)
    (fun i => (d i).positiveBase_isSupercuspidal F F.canonicalTopologicalData)
    (fun i => (d i).positiveBase_isUnitarizable F F.canonicalTopologicalData)

/-- Matching of whole segments supplies every analytic base-pair condition
for their actual midpoint bases. -/
theorem centeredSegmentBaseEulerFamily_conditions
    (hEq : SupercuspidalEqualRankLFactorStatement.{uF, max uF uV, max uF uV})
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
    {I : Type uI} {n : I → ℕ}
    {δ : letI := F.canonicalTopologicalData.topology
      ∀ i, SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (n i) F.Carrier)}
    (d : ∀ i, SquareIntegrableSegmentParameter F F.canonicalTopologicalData (n i) (δ i))
    (partner : I → I) (hseg : ∀ i, (d i).segment = (d (partner i)).segment) :
    Global.PoleComparison.BasePairConditions partner
      (fun i j => (centeredSegmentBaseEulerFamily hEq ψ ν d i j).data.reciprocal) := by
  let := F.canonicalTopologicalData.topology
  apply unitarySupercuspidalBaseFamily_conditions
    hEq ψ ν (fun i => (d i).segment.rank - 1)
    (fun i => (d i).positiveBase F F.canonicalTopologicalData)
    (fun i => ((d i).positiveBase F F.canonicalTopologicalData).representation)
    (fun i => (d i).positiveBase_isIrreducible F F.canonicalTopologicalData)
    (fun i => (d i).positiveBase_isSupercuspidal F F.canonicalTopologicalData)
    (fun i => (d i).positiveBase_isUnitarizable F F.canonicalTopologicalData)
    partner (fun i => congrArg (fun D => D.rank - 1) (hseg i))
  intro i
  exact (d i).positiveBase_equiv_of_segment_eq F F.canonicalTopologicalData
    (d (partner i)) (hseg i)

/-- A unitary generic block datum supplies both the numerical Appendix
symmetry and all analytic base-pair conditions for the chosen actual bases. -/
theorem exists_symmetric_centeredSegmentBaseEulerFamily
    (hEq : SupercuspidalEqualRankLFactorStatement.{uF, max uF uV, max uF uV})
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
    {n : ℕ} {B : BlockShape n}
    {δ : letI := F.canonicalTopologicalData.topology
      ∀ i, SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (B.size i) F.Carrier)}
    {s : Fin B.length → ℝ}
    (h : IsUnitaryGenericDatum F F.canonicalTopologicalData B δ s)
    (d : ∀ i, SquareIntegrableSegmentParameter F F.canonicalTopologicalData (B.size i) (δ i)) :
    ∃ e : Fin B.length ≃ Fin B.length,
      Global.PoleComparison.SymmetricBlockData (fun i => (d i).segment.length - 1) s e ∧
      (∀ i, (d i).segment = (d (e i)).segment) ∧
      Global.PoleComparison.BasePairConditions e
        (fun i j => (centeredSegmentBaseEulerFamily hEq ψ ν d i j).data.reciprocal) := by
  obtain ⟨e, _, hsym, hmatch⟩ :=
    h.exists_symmetricSegmentParameters F F.canonicalTopologicalData d
  have hseg := fun i => (hmatch i).1
  exact ⟨e, hsym, hseg, centeredSegmentBaseEulerFamily_conditions hEq ψ ν d e hseg⟩

end Langlands.RankinSelberg
