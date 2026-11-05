import Langlands.Representation.Classification.SegmentProductRefinement
import Langlands.Representation.Classification.SegmentProductSplit
import Langlands.Representation.Classification.SegmentCuspidalContent

/-! Actual product data for two supplied special heads. -/

noncomputable section

open CategoryTheory

namespace Langlands.Classification

open GeneralLinear PadicField.TopologicalData

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData)

/-- The supplied two-head product as actual finite product data, retaining
its complete cuspidal content and an actual equivalence of induced objects. -/
structure SegmentBinaryHeadDatum
    (Δ Γ : T.Segment.{uV,uF})
    (π : letI := T.topology
      SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier))
    (τ : letI := T.topology
      SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear Γ.degree F.Carrier)) where
  datum : T.SegmentProductDatum.{uV,uF} (Δ.degree+Γ.degree)
  heads : datum.HasSegmentHeads
  segments : List.ofFn datum.segments = [Δ,Γ]
  content : datum.multisegment.cuspidalContent =
    Δ.cuspidalContent + Γ.cuspidalContent
  equivalence : letI := T.topology
    datum.induced.representation.Equiv
      ((T.binaryNormalizedProductFunctor Δ.degree Γ.degree).obj (π,τ)).representation

set_option maxHeartbeats 800000 in
/-- Preserve the supplied actual blocks while packaging their binary product. -/
def segmentBinaryHeadDatum
    (Δ Γ : T.Segment.{uV,uF})
    (π : letI := T.topology
      SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier))
    (τ : letI := T.topology
      SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear Γ.degree F.Carrier))
    (hπ : T.IsSegmentHead Δ π) (hτ : T.IsSegmentHead Γ τ) :
    SegmentBinaryHeadDatum T Δ Γ π τ := by
  letI := T.topology
  let d : T.SegmentProductDatum.{uV,uF} (Δ.degree+Γ.degree) :=
    { length := 2
      segments := Fin.cons Δ (Fin.cons Γ Fin.elim0)
      degree_sum := by simp [Fin.sum_univ_succ]
      blocks := Fin.cases π (Fin.cases τ (fun i => Fin.elim0 i)) }
  have hd : d.HasSegmentHeads := by
    intro i
    fin_cases i
    · exact hπ
    · exact hτ
  have hsegments : List.ofFn d.segments = [Δ,Γ] := by
    simp only [d, List.ofFn_cons, List.ofFn_zero]
  have hcontent : d.multisegment.cuspidalContent =
      Δ.cuspidalContent + Γ.cuspidalContent := by
    change Multisegment.cuspidalContent
      (List.ofFn d.segments : Multiset (T.Segment.{uV,uF})) = _
    rw [hsegments]
    simp [Multisegment.cuspidalContent]
  let B := BlockShape.binary Δ.degree Γ.degree Δ.degree_pos Γ.degree_pos
  have hs : ∀ i : Fin B.length, B.size i = (d.segments (Fin.cast rfl i)).degree := by
    intro i
    fin_cases i <;> rfl
  let X := fun i : Fin B.length => (hs i).symm ▸ d.blocks (Fin.cast rfl i)
  have hbinary : (T.binaryNormalizedProductFunctor Δ.degree Γ.degree).obj (π,τ) =
      (T.normalizedProductInductionFunctor B).obj X :=
    SegmentProductSplit.binaryNormalizedProductFunctor_obj_eq T
      Δ.degree_pos Γ.degree_pos π τ X rfl rfl
  exact ⟨d,hd,hsegments,hcontent,
    (d.inducedEquivOfShape B rfl hs).trans
      (SmoothRep.equivOfIso (eqToIso hbinary.symm))⟩

end Langlands.Classification
