import Langlands.Representation.Classification.SegmentHeadProductDualInitialSupport
import Langlands.Representation.Classification.SupercuspidalSupportTwist
import Langlands.Representation.Classification.SupercuspidalSupportUniquenessProof
import Langlands.Representation.Classification.SegmentTruncationObstructionProof

/-! # Actual shifted-support witnesses for supplied special-head products -/

noncomputable section

open CategoryTheory

namespace Langlands

universe uG uF uV

namespace SmoothRep

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Exact smooth duality preserves actual subquotient occurrences. -/
theorem IsSubquotient.contragredient (hG : CompactOpenCofinal G)
    {Q A : SmoothRep.{0, uG, uV} ℂ G} (h : IsSubquotient Q A) :
    IsSubquotient Q.contragredient A.contragredient := by
  obtain ⟨C, i, q, hi, hq⟩ := isSubquotient_iff_exists.mp h
  exact Classification.CuspidalProductContragredient.isSubquotient_of_injective_of_surjective
    (contragredientHom q) (contragredientMap_injective_of_surjective _ hq)
    (contragredientHom i)
    (contragredientMap_surjective_of_injective_of_compact_cofinal hG C.isSmooth A.isSmooth _ hi)

end SmoothRep

namespace Classification

open GeneralLinear Derivative PadicField.TopologicalData
open CuspidalProductContragredient

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData)
  (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)

/-- Actual terminal and initial truncations at the original labels, with both
support multisets and their exact one-step twist equality. -/
structure SegmentHeadProductShiftedSupportData {n r : ℕ}
    (d : T.SegmentProductDatum.{uV, uF} n)
    (S E : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear r F.Carrier)) where
  terminalTruncations : Fin d.length → Option (T.Segment.{uV, uF})
  initialTruncations : Fin d.length → Option (T.Segment.{uV, uF})
  terminalSupport : Multiset (T.CuspidalDatum.{uV, uF})
  initialSupport : Multiset (T.CuspidalDatum.{uV, uF})
  terminal : ∀ i, Segment.IsTerminalTruncation (terminalTruncations i) (d.segments i)
  initial : ∀ i, Segment.IsInitialTruncation (initialTruncations i) (d.segments i)
  support_left : letI := T.topology; T.IsSupercuspidalSupport S terminalSupport
  support_dual : letI := T.topology
    letI := T.generalLinearTopologicalGroup r
    T.IsSupercuspidalSupport E.contragredient initialSupport
  terminal_union : {ρ | ρ ∈ terminalSupport} =
    ⋃ i, Segment.optionalSupport (terminalTruncations i)
  initial_union : {ρ | ρ ∈ initialSupport} =
    ⋃ i, Segment.optionalSupport (initialTruncations i)
  shifted_multiset : initialSupport = terminalSupport.map (CuspidalDatum.twist 1)

/-- Compare the actual supports of a derivative constituent and a constituent
of the derivative of the source's smooth dual, using a supplied actual dual/twist
isomorphism. Positive residual rank is explicit. -/
def chooseSegmentHeadProductShiftedSupportData {n k : ℕ}
    (hn : 0 < n) (hk : k ≤ n) (hr : 0 < n - k)
    (d : T.SegmentProductDatum.{uV, uF} n) (hd : d.HasSegmentHeads)
    (Q : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier))
    (hQ : letI := T.topology; SmoothRep.IsSubquotient Q d.induced)
    (S E : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (n - k) F.Carrier))
    (hS : letI := T.topology; S.IsIrreducible)
    (hE : letI := T.topology; E.IsIrreducible)
    (hSQ : letI := T.topology
      SmoothRep.IsSubquotient S ((generalLinearDerivative T ψ n k hk).obj Q))
    (hEQ : letI := T.topology; letI := T.generalLinearTopologicalGroup n
      SmoothRep.IsSubquotient E ((generalLinearDerivative T ψ n k hk).obj Q.contragredient))
    (e : letI := T.topology; letI := T.generalLinearTopologicalGroup (n - k)
      E.contragredient ≅ S.twist (T.determinantPowerCharacter (n - k) 1)
        (T.isOpen_ker_determinantPowerCharacter (n - k) 1)) :
    SegmentHeadProductShiftedSupportData T d S E := by
  letI := T.topology
  letI := T.generalLinearTopologicalGroup n
  letI := T.generalLinearTopologicalGroup (n - k)
  apply Classical.choice
  obtain ⟨A, s, hA, hs, hAs⟩ :=
    segmentHeadProductTerminalTruncationUnionOfSubquotient T ψ hn hk d hd Q hQ S hS hSQ
  have hQdual := hQ.contragredient (compactOpen_cofinal F T n)
  let w := segmentHeadProductDualInitialSupportDataOfSubquotient T ψ hn hk d hd
    Q.contragredient hQdual E hE hEQ
  have hS_twist := (SmoothRep.isIrreducible_twist_iff
    (T.determinantPowerCharacter (n - k) 1)
    (T.isOpen_ker_determinantPowerCharacter (n - k) 1) S).mpr hS
  have hshift : (∑ i, w.supports i) = s.map (CuspidalDatum.twist 1) :=
    glSupercuspidalSupportUniqueness.{uV, uF} p F T (n - k) hr _ hS_twist _ _
      (w.support.of_iso e) (hs.twist 1)
  exact ⟨{
    terminalTruncations := A
    initialTruncations := w.truncations
    terminalSupport := s
    initialSupport := ∑ i, w.supports i
    terminal := hA
    initial := w.initial
    support_left := hs
    support_dual := w.support
    terminal_union := hAs
    initial_union := SegmentHeadProductDualInitialSupportData.support_union T w
    shifted_multiset := hshift }⟩

namespace SegmentHeadProductShiftedSupportData

variable {T} {n r : ℕ} {d : T.SegmentProductDatum.{uV, uF} n}
  {S E : letI := T.topology
    SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear r F.Carrier)}
  (w : SegmentHeadProductShiftedSupportData T d S E)

/-- The retained multiset comparison yields exactly the union comparison used
by the finite truncation obstruction. -/
theorem shifted_union :
    (⋃ i, Segment.optionalSupport (w.initialTruncations i)) =
      (CuspidalDatum.twist 1) ''
        (⋃ i, Segment.optionalSupport (w.terminalTruncations i)) := by
  rw [← w.initial_union, ← w.terminal_union, w.shifted_multiset]
  ext ρ
  simp only [Set.mem_ofPred_eq, Multiset.mem_map, Set.mem_image]

/-- Positive residual rank forces a nonempty initial-support union. -/
theorem initial_union_nonempty (hr : 0 < r) :
    (⋃ i, Segment.optionalSupport (w.initialTruncations i)).Nonempty := by
  have hne : w.initialSupport ≠ 0 := by
    intro hzero
    have hsum := w.support_dual.sum_rank
    rw [hzero, Multiset.map_zero, Multiset.sum_zero] at hsum
    omega
  obtain ⟨ρ, hρ⟩ := Multiset.exists_mem_of_ne_zero hne
  exact ⟨ρ, (Set.ext_iff.mp w.initial_union ρ).mp hρ⟩

include w in
/-- The actual support comparison at positive residual rank forces a linked
pair of the original labels. -/
theorem exists_linked_pair (hr : 0 < r) :
    ∃ i j : Fin d.length, (d.segments i).IsLinked (d.segments j) :=
  segmentTruncationObstruction.{uF, uV} F T d.length d.segments
    w.terminalTruncations w.initialTruncations w.terminal w.initial
    w.shifted_union (w.initial_union_nonempty hr)

end SegmentHeadProductShiftedSupportData

end Classification

end Langlands
