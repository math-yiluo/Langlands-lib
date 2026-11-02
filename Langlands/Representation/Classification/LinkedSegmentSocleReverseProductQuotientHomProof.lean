import Langlands.Representation.Classification.LinkedSegmentOverlapCase
import Langlands.Representation.Classification.LinkedSegmentOverlapSplit
import Langlands.Representation.Classification.JuxtaposedSegmentSocleReverseProductStructureProof
import Langlands.Representation.Classification.SegmentSocleJacquetProof
import Langlands.Representation.Geometric.IdentityCellQuotientProof

/-!
# Zelevinsky's Proposition 4.6, step (2)

For segment socles of `Δ'` preceding `Δ`, there is a nonzero intertwiner
`⟨Δ⟩ × ⟨Δ'⟩ → ⟨Δ ∪ Δ'⟩ × ⟨Δ ∩ Δ'⟩`. The juxtaposed case is step (1); the
overlapping case splits `Δ'` and uses the identity-cell quotient (Ze80 1.3) and
the Jacquet module of a segment socle (Ze80 3.4).
-/

set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace Langlands.Classification

open PadicField.TopologicalData QuotientHom

universe uF uV

section Conditional

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} {T : F.TopologicalData}

/-- Ze80 4.6 step (2), from step (1), Ze80 3.4 and the identity-cell quotient
Ze80 1.3. -/
theorem linkedSegmentSocleReverseProductQuotientHom_of
    (h1 : JuxtaposedSegmentSocleReverseProductStructure.{uF, uV} F T)
    (h34 : SegmentSocleJacquetFormula.{uF, uV} F T)
    (h13 : Geometric.PadicIdentityCellQuotientTheorem.{uF, max uF uV}) :
    LinkedSegmentSocleReverseProductQuotientHom.{uF, uV} F T := by
  intro n d h₂ hd hp U I e hs he he'
  cases I with
  | none => exact exists_ne_zero_of_juxtaposed h1 d h₂ hd hp U e hs he he'
  | some J =>
    obtain ⟨q, hq, hqm, hJ, hpre, hjux, hrep, hdeg⟩ := exists_overlap_split hp hs
    exact exists_ne_zero_of_overlap h1 h34 h13 d h₂ hd U J e q hq hqm hJ hpre hjux hrep
      hdeg he he'

end Conditional

/-- Zelevinsky 1980, Proposition 4.6, step (2): if `Δ'` precedes `Δ`, then
`Hom(⟨Δ⟩ × ⟨Δ'⟩, ⟨Δ ∪ Δ'⟩ × ⟨Δ ∩ Δ'⟩) ≠ 0` for every socle datum of the union
followed by the optional intersection. -/
theorem linkedSegmentSocleReverseProductQuotientHom
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData) :
    LinkedSegmentSocleReverseProductQuotientHom.{uF, uV} F T :=
  linkedSegmentSocleReverseProductQuotientHom_of
    (juxtaposedSegmentSocleReverseProductStructure.{uF, uV} F T)
    (segmentSocleJacquetFormula.{uF, uV} F T)
    Geometric.padicIdentityCellQuotientTheorem.{uF, max uF uV}

end Langlands.Classification
