import Langlands.Representation.Classification.SquareIntegrableInductionIrreducibilityStatement
import Langlands.Representation.Classification.SegmentEssentialSquareIntegrableClassificationProof
import Langlands.Representation.Classification.SquareIntegrableSegmentNonlinkageProof
import Langlands.Representation.Classification.SegmentHeadProductIrreducibilityProof

/-!
# Irreducibility of normalized induction of square-integrable blocks

Classify the original analytic blocks as special segment heads, apply
nonlinkage and the segment-product criterion, and eliminate only the equalities
between their segment degrees and the original ordered block sizes.
-/

noncomputable section

open CategoryTheory Langlands.GeneralLinear

namespace Langlands.Classification

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

/-- Keep the supplied blocks in their original order, changing only rank indices. -/
private def segmentDatum {n : ℕ} (B : BlockShape n)
    (σ : letI := T.topology; ∀ i,
      SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear (B.size i) F.Carrier))
    (Δ : Fin B.length → T.Segment.{max uF uV,uF})
    (h : ∀ i, (Δ i).degree = B.size i) :
    T.SegmentProductDatum.{max uF uV,uF} n where
  length := B.length
  segments := Δ
  degree_sum := (Finset.sum_congr rfl fun i _ => h i).trans B.sum_eq
  blocks i := (h i).symm ▸ σ i

/-- Equality of block sizes identifies the actual normalized induction functors. -/
private theorem segmentDatum_induced_iso {n : ℕ} (B : BlockShape n)
    (σ : letI := T.topology; ∀ i,
      SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear (B.size i) F.Carrier))
    (Δ : Fin B.length → T.Segment.{max uF uV,uF})
    (h : ∀ i, (Δ i).degree = B.size i) :
    letI := T.topology
    Nonempty ((segmentDatum T B σ Δ h).induced ≅
      (T.normalizedProductInductionFunctor B).obj σ) := by
  let := T.topology
  rcases B with ⟨r, sizes, positive, sum_eq⟩
  dsimp at Δ h σ ⊢
  have hh : (fun i => (Δ i).degree) = sizes := funext h
  cases hh
  exact ⟨Iso.refl _⟩

/-- Equality transport in the natural rank preserves analytic square-integrability. -/
private theorem squareIntegrable_rank_cast {a b : ℕ} (h : a = b)
    (π : letI := T.topology;
      SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear a F.Carrier))
    (hπ : letI := T.topology; T.IsSquareIntegrable π.representation) :
    letI := T.topology; T.IsSquareIntegrable (h ▸ π).representation := by
  subst b
  exact hπ

set_option maxHeartbeats 800000 in
/-- The actual ordered normalized upper induction of the supplied blocks is
algebraically irreducible. -/
theorem squareIntegrableBlockInductionIrreducibility
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData) :
    SquareIntegrableBlockInductionIrreducibility.{uF,uV} F T := by
  classical
  let := T.topology
  intro n hn
  cases n with
  | zero => exact (Nat.lt_irrefl 0 hn).elim
  | succ n =>
    intro B σ hσ
    have hs := fun i =>
      (segmentEssentialSquareIntegrableClassification.{uF,uV} F T
        (B.size i) (B.positive i) (σ i) (hσ i).1).mp
          (hσ i).2.1.isEssentiallySquareIntegrable
    choose Δ hdegree hhead using hs
    let d := segmentDatum T B σ Δ hdegree
    have hd : d.HasSegmentHeads := hhead
    have hu : d.multisegment.IsUnlinked := by
      intro A hA A' hA'
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hA
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hA'
      apply squareIntegrableSegmentNonlinkage.{uF,uV} T
        (Δ i) (Δ j) _ _ (hhead i) (hhead j)
      · exact squareIntegrable_rank_cast T (hdegree i).symm _ (hσ i).2.1
      · exact squareIntegrable_rank_cast T (hdegree j).symm _ (hσ j).2.1
    have hi := (segmentHeadProductIrreducibility.{uF,max uF uV} F T n d hd).mpr hu
    obtain ⟨e⟩ := segmentDatum_induced_iso T B σ Δ hdegree
    exact (Weil.IsomorphismInvariance.irreducible_iff (SmoothRep.equivOfIso e)).mp hi

end Langlands.Classification
