import Langlands.Representation.Aubert.IrreducibleImageStatement
import Langlands.Representation.Aubert.SegmentSocleHeadStatement
import Langlands.Representation.Aubert.SegmentSignedJacquetHead

/-! Segment exchange conditional on an actual irreducible Aubert image. -/

noncomputable section

namespace Langlands.Aubert

open GeneralLinear SegmentFullJacquet CuspidalSupport Parabolic

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- An actual signed irreducible image of the supplied segment socle suffices
for the exact segment exchange. The signed-image equality is an explicit
hypothesis, and is not proved by this reduction. -/
theorem segmentSocleHead_of_signedIrreducibleImage
    (Δ : T.Segment.{max uF uV, uF})
    (πZ πS τ : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier))
    (hZ : T.IsSegmentSocle Δ πZ) (hS : T.IsSegmentHead Δ πS)
    (hτ : letI := T.topology; τ.IsIrreducible)
    (δ : ℤ) (hδ : δ = 1 ∨ δ = -1)
    (hImage : letI := T.topology
      alternatingOperator.{uF, uV} F T Δ.degree
          (GeneralLinear.finiteLengthClass Δ.degree F.Carrier πZ
            (SmoothRep.hasFiniteLength_of_isIrreducible (by
              obtain ⟨_, _, h⟩ := hZ
              exact h.1))) =
        δ • GeneralLinear.finiteLengthClass Δ.degree F.Carrier τ
          (SmoothRep.hasFiniteLength_of_isIrreducible hτ)) :
    letI := T.topology
    alternatingOperator.{uF, uV} F T Δ.degree
        (GeneralLinear.finiteLengthClass Δ.degree F.Carrier πZ
          (SmoothRep.hasFiniteLength_of_isIrreducible (by
            obtain ⟨_, _, h⟩ := hZ
            exact h.1))) =
      (-1 : ℤ) ^ (Δ.degree - Δ.length) •
        GeneralLinear.finiteLengthClass Δ.degree F.Carrier πS
          (SmoothRep.hasFiniteLength_of_isIrreducible (by
            obtain ⟨_, _, h⟩ := hS
            exact h.1)) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let B := BlockShape.uniform Δ.length Δ.rank Δ.rank_pos
  let s : ℤ := (-1 : ℤ) ^ (Δ.degree - Δ.length)
  have hs : s = 1 ∨ s = -1 := neg_one_pow_eq_or ℤ _
  have hδsq : δ * δ = 1 := by
    rcases hδ with rfl | rfl <;> norm_num
  obtain ⟨A, hA, hZi, j, hj⟩ := hZ.isSegmentSubrepresentation
  have hZweak : T.IsSegmentSubrepresentation Δ πZ := ⟨A, hA, hZi, j, hj⟩
  have hZfl := SmoothRep.hasFiniteLength_of_isIrreducible hZi
  have hτfl := SmoothRep.hasFiniteLength_of_isIrreducible hτ
  have hSfl := SmoothRep.hasFiniteLength_of_isIrreducible (by
    obtain ⟨_, _, h⟩ := hS
    exact h.1)
  have hqc := subrepresentationJacquet_isLeviQuasicuspidal
    F T πZ hZweak A hA
  have hqcRev : IsLeviQuasicuspidal B.reverse
      ((T.normalizedJacquetFunctor B.reverse).obj πZ).representation := by
    change IsLeviQuasicuspidal B
      ((T.normalizedJacquetFunctor B.reverse).obj πZ).representation
    rw [uniformJacquetObject_reverse_eq F T Δ.rank_pos πZ]
    exact hqc
  have hJτ := normalizedJacquetK0_hasFiniteLength F T B τ hτfl
  have hR := reversedJacquetObject_hasFiniteLength F T B πZ hZfl
  have hExchange := quasicuspidalJacquetExchange F T Δ.degree B πZ hZfl hqcRev
  rw [hImage, map_smul,
    normalizedJacquetK0_finiteLengthClass F T B τ hτfl hJτ] at hExchange
  change δ • B.finiteLengthClass F.Carrier
      ((T.normalizedJacquetFunctor B).obj τ) hJτ =
    s • B.finiteLengthClass F.Carrier
      (reversedJacquetObject F T B πZ) hR at hExchange
  have hEq : B.finiteLengthClass F.Carrier
      ((T.normalizedJacquetFunctor B).obj τ) hJτ =
    (δ * s) • B.finiteLengthClass F.Carrier
      (reversedJacquetObject F T B πZ) hR := by
    calc
      _ = δ • (δ • B.finiteLengthClass F.Carrier
          ((T.normalizedJacquetFunctor B).obj τ) hJτ) := by
        rw [smul_smul, hδsq, one_smul]
      _ = δ • (s • B.finiteLengthClass F.Carrier
          (reversedJacquetObject F T B πZ) hR) :=
        congrArg (fun x => δ • x) hExchange
      _ = _ := smul_smul _ _ _
  have hδs : δ * s = 1 ∨ δ * s = -1 := by
    rcases hδ with hδ | hδ <;> rcases hs with hs | hs <;> simp [hδ, hs]
  obtain ⟨hSign, ⟨e⟩⟩ := segmentHead_of_signedJacquetClass F T
    Δ πZ πS τ hZweak hS hτ (δ * s) hδs hEq
  have hδsEq : δ = s := by
    calc
      δ = δ * 1 := (mul_one δ).symm
      _ = δ * (δ * s) := by rw [hSign]
      _ = (δ * δ) * s := (mul_assoc _ _ _).symm
      _ = s := by rw [hδsq, one_mul]
  have hClass := SmoothRep.FiniteLengthGrothendieckGroup.ofRepresentation_eq_of_equiv
    hτfl hSfl e
  change GeneralLinear.finiteLengthClass Δ.degree F.Carrier τ hτfl =
    GeneralLinear.finiteLengthClass Δ.degree F.Carrier πS hSfl at hClass
  rw [hImage, hδsEq, hClass]

/-- The general irreducible-image assertion implies the exact segment
socle-to-special-head assertion. This is an explicit intermediate implication. -/
def SegmentSocleHeadReductionStatement : Prop :=
  IrreducibleImageStatement.{uF, uV} F T →
    SegmentSocleHeadStatement.{uF, uV} F T

theorem segmentSocleHead_of_irreducibleImage :
    SegmentSocleHeadReductionStatement.{uF, uV} F T := by
  let := T.topology
  intro hImage Δ πZ πS hZ hS
  have hZi : πZ.IsIrreducible := by
    obtain ⟨_, _, h⟩ := hZ
    exact h.1
  obtain ⟨τ, hτ, hτImage⟩ := hImage Δ.degree πZ hZi
  rcases hτImage with hτImage | hτImage
  · exact segmentSocleHead_of_signedIrreducibleImage F T
      Δ πZ πS τ hZ hS hτ 1 (Or.inl rfl) (by
        simpa only [one_smul] using hτImage)
  · exact segmentSocleHead_of_signedIrreducibleImage F T
      Δ πZ πS τ hZ hS hτ (-1) (Or.inr rfl) (by
        simpa only [neg_one_smul] using hτImage)

end Langlands.Aubert
