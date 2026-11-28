import Langlands.AllFieldBZ.Representation.Classification.OrderedSegmentProducts
import Langlands.AllFieldBZ.Representation.Jacquet.Parabolic

/-! Subsegment tensor factors of normalized Jacquet restriction at divisible blocks. -/

namespace Langlands.AllFieldBZ.Classification

open Langlands.GeneralLinear LocalFieldPackage.TopologicalData

universe uF uV

/-- Each divisible block receives the corresponding contiguous subsegment
of the increasing order for the socle and the decreasing order for the head. -/
def DivisibleBlockSegmentJacquetStatement (F : LocalFieldPackage.{uF})
    (T : F.TopologicalData) : Prop :=
  letI := T.topology
  ∀ (Δ : Segment.{uV, uF} T)
    (π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier))
    (B : BlockShape Δ.degree), (∀ i, Δ.rank ∣ B.size i) →
    let count (i : Fin B.length) := B.size i / Δ.rank
    let startIncreasing (i : Fin B.length) := ∑ j : Fin B.length with j < i, count j
    let HasFactors
        (start : Fin B.length → ℕ)
        (Endpoint : (Γ : Segment.{uV, uF} T) →
          SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Γ.degree F.Carrier) → Prop) : Prop :=
      ∃ (Γ : Fin B.length → Segment.{uV, uF} T)
        (hdeg : ∀ i, (Γ i).degree = B.size i)
        (σ : ∀ i, SmoothRep.{0, uF, max uF uV} ℂ
          (GeneralLinear (B.size i) F.Carrier)),
        (∀ i, (Γ i).length = count i ∧ (Γ i).base = Δ.member (start i) ∧
          Endpoint (Γ i) ((hdeg i).symm ▸ σ i)) ∧
        Nonempty (((T.normalizedJacquetFunctor B).obj π).representation.Equiv
          (FiniteTensor.externalSmoothObject σ).representation)
    (T.IsSegmentSocle Δ π → HasFactors startIncreasing T.IsSegmentSocle) ∧
      (T.IsSegmentHead Δ π →
        HasFactors (fun i => Δ.length - startIncreasing i - count i) T.IsSegmentHead)

end Langlands.AllFieldBZ.Classification
