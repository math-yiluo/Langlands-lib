import Langlands.Analysis.Local.CompactQuotientDiscreteDecompositionStatement
import Langlands.Analysis.Local.CompactQuotientHilbertSchmidtProof
import Langlands.Analysis.HilbertSchmidtCompactProof
import Langlands.Representation.Unitary.InvariantSubspaceDiscreteDecompositionProof

/-! # Discrete decomposition on a compact left coset space -/

noncomputable section

universe uG

namespace Langlands.QuotientIntegration

open MeasureTheory
open Langlands.Analysis Langlands.Analysis.OperatorIdeals

/-- The compact quotient has a Hilbert sum of irreducible subrepresentations
of the original action, with finite multiplicities. -/
theorem compactQuotientDiscreteDecomposition :
    CompactQuotientDiscreteDecompositionStatement.{uG} := by
  intro G _ _ _ _ _ _ _ _ H hH _ _ μH _ _ _ _ _ μG _ ν _ hν hcompact
    π hπinner hπcont hπapply
  let E := Lp ℂ 2 ν
  have hπnorm (g : G) (x : E) : ‖π g x‖ = ‖x‖ :=
    (LinearMap.norm_map_iff_inner_map_map (π g)).2 (hπinner g) x
  have hπmeas (x : E) : AEStronglyMeasurable (fun g => π g x) μG :=
    (hπcont x).stronglyMeasurable.aestronglyMeasurable
  have hHS := compactQuotientIntegratedHilbertSchmidt H hH μH μG ν hν hcompact
    π hπnorm hπmeas hπapply
  obtain ⟨A, hgood, hpair, hspan, hfin⟩ :=
    invariantSubspaceDiscreteDecomposition μG π hπinner hπcont
      (⊤ : Submodule ℂ E) isClosed_univ (fun _ _ _ => Submodule.mem_top) (fun f hf =>
        (hilbertSchmidtCompact E E _ (hHS f hf)).comp_clm _)
  let (P : A) : CompleteSpace ↥P.val :=
    (hgood P.val P.property).2.2.1.completeSpace_coe
  have horth : OrthogonalFamily ℂ (fun P : A => ↥P.val) (fun P => P.val.subtypeₗᵢ) := by
    apply orthogonalFamily_iff_pairwise.mpr
    intro P Q hPQ
    exact hpair P.property Q.property (fun h => hPQ (Subtype.ext h))
  have htotal : (⨆ P : A, P.val).topologicalClosure = ⊤ := by
    rwa [← sSup_eq_iSup']
  exact ⟨A, fun P hP => (hgood P hP).2,
    IsHilbertSum.mkInternal (fun P : A => P.val) horth htotal.ge, hfin⟩

end Langlands.QuotientIntegration
