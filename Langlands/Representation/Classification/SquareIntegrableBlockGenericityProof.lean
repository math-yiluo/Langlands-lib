import Langlands.Representation.Classification.TemperedBlockStatement
import Langlands.Representation.Classification.SegmentEssentialSquareIntegrableClassificationProof
import Langlands.Representation.Classification.SquareIntegrableSegmentNonlinkageProof
import Langlands.Representation.Classification.GenericSegmentProductExhaustionProof

/-!
# Genericity of square-integrable block products

Classify the supplied analytic blocks as strong segment heads. Their segments
are unlinked, and the reverse generic segment-product theorem applies to the
same ordered normalized product.
-/

noncomputable section

namespace Langlands.Classification

open CategoryTheory GeneralLinear PadicField.TopologicalData

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

private theorem squareIntegrable_rank_transport {a b : ℕ} (h : a = b)
    (π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear a F.Carrier))
    (hπ : letI := T.topology; T.IsSquareIntegrable π.representation) :
    letI := T.topology; T.IsSquareIntegrable (h ▸ π).representation := by
  subst b
  exact hπ

set_option maxHeartbeats 800000 in
/-- Replacing block sizes by equal segment degrees preserves the actual
normalized induced object, with its supplied blocks transported accordingly. -/
private theorem segmentShape_induced_eq {n : ℕ} (B : BlockShape n)
    (Δ : Fin B.length → T.Segment.{max uF uV, uF})
    (hΔ : ∀ i, (Δ i).degree = B.size i)
    (σ : letI := T.topology
      ∀ i, SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (B.size i) F.Carrier)) :
    letI := T.topology
    (T.normalizedProductInductionFunctor
      (T.segmentShape Δ ((Finset.sum_congr rfl (fun i _ => hΔ i)).trans B.sum_eq))).obj
        (fun i => (show SmoothRep.{0, uF, max uF uV} ℂ
          (GeneralLinear (Δ i).degree F.Carrier) from (hΔ i).symm ▸ σ i)) =
      (T.normalizedProductInductionFunctor B).obj σ := by
  rcases B with ⟨r, size, positive, sum_eq⟩
  dsimp only at Δ hΔ σ
  have he : (fun i => (Δ i).degree) = size := funext hΔ
  subst size
  rfl

set_option maxHeartbeats 800000 in
/-- Every normalized product of irreducible square-integrable unitarizable
blocks is generic for every allowed additive character. -/
theorem squareIntegrableBlockGenericity :
    SquareIntegrableBlockGenericity.{uF, uV} F T := by
  classical
  let := T.topology
  intro n B σ hσ ψ
  choose Δ hΔ hhead using fun i =>
    (segmentEssentialSquareIntegrableClassification.{uF, uV} F T
      (B.size i) (B.positive i) (σ i) (hσ i).1).mp
        (hσ i).2.1.isEssentiallySquareIntegrable
  let d : T.SegmentProductDatum.{max uF uV, uF} (n + 1) :=
    ⟨B.length, Δ, (Finset.sum_congr rfl (fun i _ => hΔ i)).trans B.sum_eq,
      fun i => (hΔ i).symm ▸ σ i⟩
  have hd : d.HasSegmentHeads := hhead
  have hsquare (i : Fin B.length) :
      T.IsSquareIntegrable (d.blocks i).representation :=
    squareIntegrable_rank_transport F T (hΔ i).symm (σ i) (hσ i).2.1
  have hunlinked : d.multisegment.IsUnlinked := by
    intro Γ hΓ Γ' hΓ'
    simp only [SegmentProductDatum.multisegment, Multiset.mem_coe,
      List.mem_ofFn] at hΓ hΓ'
    obtain ⟨i, rfl⟩ := hΓ
    obtain ⟨j, rfl⟩ := hΓ'
    exact squareIntegrableSegmentNonlinkage.{uF, uV} T
      (d.segments i) (d.segments j) (d.blocks i) (d.blocks j)
      (hd i) (hd j) (hsquare i) (hsquare j)
  have heq : d.induced = (T.normalizedProductInductionFunctor B).obj σ :=
    segmentShape_induced_eq F T B Δ hΔ σ
  exact (genericSegmentProductExhaustion.{uF, uV} T ψ n
    ((T.normalizedProductInductionFunctor B).obj σ)).mpr
      ⟨d, hd, hunlinked, ⟨eqToIso heq.symm⟩⟩

end Langlands.Classification
