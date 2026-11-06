import Langlands.Geometry.Analytic.StrictTestDomain.IdealCoverDescent
import Langlands.Geometry.Analytic.StrictTestDomain.BinaryLaurentCover

/-! # The ideal descent chase across an actual Laurent split -/

noncomputable section

universe u v

namespace Langlands.Analytic.StrictTestDomain

open CategoryTheory RationalData

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {P : PresentedStrictAffinoidAlgebra K}

/-- Effectiveness for two prescribed rational domains, expressed as existence
of a global ideal with the prescribed closed local extensions. -/
def BinaryIdealDescent (d e : RationalData K P) : Prop :=
  ∀ (I : Ideal d.algebra) (J : Ideal e.algebra),
    (interLeft d e).restriction.closedIdealMap I =
      (interRight d e).restriction.closedIdealMap J →
    ∃ H : Ideal P, d.baseMap.closedIdealMap H = I ∧ e.baseMap.closedIdealMap H = J

private theorem extension_eq_on_smaller (d e t : RationalData K P) (inc : t ⟶ e)
    (J : Ideal e.algebra) (I : Ideal d.algebra)
    (h : (d.pullback e.baseMap).baseMap.closedIdealMap J =
      (d.comparison e.baseMap).closedIdealMap I) :
    (d.pullback t.baseMap).baseMap.closedIdealMap (inc.restriction.closedIdealMap J) =
      (d.comparison t.baseMap).closedIdealMap I := by
  let m := d.pullbackTriangleMap e.baseMap t.baseMap inc.restriction
    inc.restriction_comp_baseMap
  rw [BoundedAlgHom.closedIdealMap_comp,
    ← d.pullbackTriangleMap_comp_baseMap e.baseMap t.baseMap inc.restriction
      inc.restriction_comp_baseMap,
    ← BoundedAlgHom.closedIdealMap_comp, h, BoundedAlgHom.closedIdealMap_comp,
    pullbackTriangleMap_comp_comparison]

private theorem pullback_base_ideals_eq (d e : RationalData K P)
    (H : Ideal P) (I : Ideal d.algebra)
    (h : (d.pullback e.baseMap).baseMap.closedIdealMap (e.baseMap.closedIdealMap H) =
      (d.comparison e.baseMap).closedIdealMap I) :
    (e.pullback d.baseMap).baseMap.closedIdealMap (d.baseMap.closedIdealMap H) =
      (e.pullback d.baseMap).baseMap.closedIdealMap I := by
  have h' := congrArg ((d.pullbackSwapMap e).closedIdealMap) h
  rw [BoundedAlgHom.closedIdealMap_comp, BoundedAlgHom.closedIdealMap_comp,
    BoundedAlgHom.closedIdealMap_comp,
    pullbackSwapMap_comp_baseMap, pullbackSwapMap_comp_comparison,
    comparison_comp_baseMap, ← BoundedAlgHom.closedIdealMap_comp] at h'
  exact h'

/-- Ideal effectiveness on the two coefficient-pulled families, together with
the actual binary Laurent ideal theorem, implies effectiveness on the original
finite rational point cover. -/
theorem laurentSplitIdealDescent (hK : ∃ c : K, 1 < ‖c‖)
    {ι : Type v} [Finite ι] (D : ι → RationalData K P)
    (hD : ∀ x : BanachSpectrum P, ∃ i, x ∈ (D i).locus) (f : P)
    (hbin : BinaryIdealDescent (laurentUpper f) (laurentLower f))
    (hU : IdealCoverDescent (fun i => (D i).pullback (laurentUpper f).baseMap))
    (hL : IdealCoverDescent (fun i => (D i).pullback (laurentLower f).baseMap)) :
    IdealCoverDescent D := by
  intro I hI
  let U := laurentUpper f
  let L := laurentLower f
  let O := U.inter L
  let IU := fun i => ((D i).comparison U.baseMap).closedIdealMap (I i)
  let IL := fun i => ((D i).comparison L.baseMap).closedIdealMap (I i)
  let JU := idealSectionContraction (fun i => (D i).pullback U.baseMap) IU
  let JL := idealSectionContraction (fun i => (D i).pullback L.baseMap) IL
  have heffU := hU IU (hI.comparison U.baseMap)
  have heffL := hL IL (hI.comparison L.baseMap)
  have hcompat : (interLeft U L).restriction.closedIdealMap JU =
      (interRight U L).restriction.closedIdealMap JL := by
    apply (idealCoverSeparated_of_covers hK (fun i => (D i).pullback O.baseMap)
      (fun x => hD (BanachSpectrum.comap O.baseMap.toBoundedRingHom x))).eq_of_extensions
    intro i
    exact (extension_eq_on_smaller (D i) U O (interLeft U L) JU (I i) (heffU i)).trans
      (extension_eq_on_smaller (D i) L O (interRight U L) JL (I i) (heffL i)).symm
  obtain ⟨H, hHU, hHL⟩ := hbin JU JL hcompat
  have hlocal : ∀ i, (D i).baseMap.closedIdealMap H = I i := by
    intro i
    let E : Bool → RationalData K (D i).algebra := fun b =>
      (if b then L else U).pullback (D i).baseMap
    have hE : ∀ x : BanachSpectrum (D i).algebra, ∃ b, x ∈ (E b).locus := by
      intro x
      rcases mem_laurentUpper_or_mem_laurentLower f
          (BanachSpectrum.comap (D i).baseMap.toBoundedRingHom x) with hx | hx
      · exact ⟨false, hx⟩
      · exact ⟨true, hx⟩
    apply (idealCoverSeparated_of_covers hK E hE).eq_of_extensions
    intro b
    cases b with
    | false =>
        apply pullback_base_ideals_eq (D i) U H (I i)
        rw [hHU]
        exact heffU i
    | true =>
        apply pullback_base_ideals_eq (D i) L H (I i)
        rw [hHL]
        exact heffL i
  have hcontract : idealSectionContraction D I = H := by
    ext a
    rw [mem_idealSectionContraction]
    constructor
    · intro ha
      apply idealCoverSeparated_of_covers hK D hD H a
      intro i
      rw [hlocal i]
      exact ha i
    · intro ha i
      rw [← hlocal i]
      exact (D i).baseMap.mem_closedIdealMap ha
  intro i
  rw [hcontract]
  exact hlocal i

end Langlands.Analytic.StrictTestDomain
