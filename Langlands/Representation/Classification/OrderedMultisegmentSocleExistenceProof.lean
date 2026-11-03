import Langlands.Representation.Classification.OrderedMultisegmentSocleAdapter
import Langlands.Representation.Classification.OrderedMultisegmentSocleBoundaryProof
import Langlands.Representation.Classification.SegmentSocleProductHomogeneityProof
import Langlands.Representation.Classification.SegmentInitialTruncationOrderProof
import Langlands.Representation.Filtration.RepresentationLength
import Langlands.HarmonicAnalysis.PadicUnitaryAdditiveCharacterExistsProof

/-! # Independent unique socles of ordered segment products -/

noncomputable section

open CategoryTheory

namespace Langlands.Classification

open PadicField.TopologicalData Derivative

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

private theorem stronglyIndecomposable_of_iso
    {G : Type uF} [Group G] [TopologicalSpace G]
    {A B : SmoothRep.{0, uF, max uF uV} ℂ G}
    (e : A ≅ B) (hB : IsStronglyIndecomposable B.representation) :
    IsStronglyIndecomposable A.representation := by
  let e' := (Subrepresentation.subrepresentationSubmoduleOrderIso
    (ρ := A.representation)).trans
      ((Submodule.orderIsoMapComap (repAsModuleEquiv (SmoothRep.equivOfIso e))).trans
        (Subrepresentation.subrepresentationSubmoduleOrderIso
          (ρ := B.representation)).symm)
  exact (stronglyIndecomposable_iff_of_orderIso e').mpr hB

private theorem dropLastList_eq_filterMap (l : List (Segment.{max uF uV, uF} T)) :
    Segment.dropLastList l =
      l.filterMap (fun Δ =>
        if h : 2 ≤ Δ.length then
          some (⟨Δ.base, Δ.length - 1, by omega⟩ : Segment.{max uF uV, uF} T)
        else none) := rfl

private theorem orderedSegmentProduct_stronglyIndecomposable
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology) :
    letI := T.topology
    ∀ (n : ℕ) (d : T.SegmentProductDatum.{max uF uV, uF} n),
      d.IsPrecedenceOrdered → d.HasSegmentSocles →
      IsStronglyIndecomposable d.induced.representation := by
  let := T.topology
  have hfree := cuspidalIntegralTwistFreeness.{uF, max uF uV} F T
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro d ho hs
    cases n with
    | zero =>
      let : d.induced.IsIrreducible :=
        (orderedMultisegmentSocle_rankZero.{uF, uV} F T d ho hs).2.2.1
      intro S U hS hU
      rw [(eq_bot_or_eq_top S).resolve_left hS, (eq_bot_or_eq_top U).resolve_left hU]
      simpa only [inf_top_eq] using
        (top_ne_bot : (⊤ : Subrepresentation d.induced.representation) ≠ ⊥)
    | succ N =>
      let k := ∑ i, (d.segments i).rank
      have hk : k ≤ N + 1 := by
        calc
          k ≤ ∑ i, (d.segments i).degree := Finset.sum_le_sum fun i _ => by
            simpa using Nat.mul_le_mul_right (d.segments i).rank (d.segments i).length_pos
          _ = N + 1 := d.degree_sum
      have hlen : 0 < d.length := by
        by_contra h
        have hl : d.length = 0 := by omega
        have hz : (∑ i, (d.segments i).degree) = 0 := by simp [hl]
        have := d.degree_sum
        omega
      have hkpos : 0 < k := by
        calc
          0 < (d.segments ⟨0, hlen⟩).rank := (d.segments ⟨0, hlen⟩).rank_pos
          _ ≤ k := Finset.single_le_sum
            (f := fun i : Fin d.length => (d.segments i).rank)
            (fun _ _ => Nat.zero_le _) (Finset.mem_univ (⟨0, hlen⟩ : Fin d.length))
      have hcalc := segmentSocleProductHighestDerivative.{uF, max uF uV}
        F T ψ (N + 1) d hs k hk rfl
      obtain ⟨d', hlist, hs', ⟨e⟩⟩ := hcalc.2.1
      have ho' : d'.IsPrecedenceOrdered := by
        apply (T.isPrecedenceOrdered_iff_list d'.segments).mpr
        rw [← dropLastList_eq_filterMap F T] at hlist
        rw [hlist]
        exact (segmentInitialTruncationOrder.{uF, max uF uV} F T hfree).2
          (List.ofFn d.segments) ((T.isPrecedenceOrdered_iff_list d.segments).mp ho)
      have hSI' := ih (N + 1 - k) (by omega) d' ho' hs'
      have hSI := stronglyIndecomposable_of_iso.{uF, uV} e hSI'
      have hnonzero' := segmentSocleProduct_nontrivial.{uF, uV} F T d' hs'
      have hnonzero :
          Nontrivial ((generalLinearDerivative T ψ (N + 1) k hk).obj d.induced) := by
        let := hnonzero'
        exact (SmoothRep.equivOfIso e).toLinearEquiv.toEquiv.nontrivial
      have hk' : 0 < k ∧ k ≤ N + 1 := ⟨hkpos, hk⟩
      have hderivEq :
          (generalLinearDerivative T ψ (N + 1) k hk).obj d.induced =
            (mirabolicDerivativeOfOrder T ψ N k hk').obj
              ((generalLinearRestriction T N).obj d.induced) := by
        simpa only [generalLinearRankCast_refl, Functor.id_obj] using
          RestrictionBridge.generalLinearDerivative_obj_eq_cast
            T ψ (a := N + 1) (n := N) (k := k) rfl hk hk' rfl d.induced
      have hlevel :
          level T ψ ((generalLinearRestriction T N).obj d.induced) = k := by
        apply (level_eq_iff T ψ hkpos _).mpr
        refine ⟨hk, ⟨hk', ?_⟩, ?_⟩
        · rwa [← hderivEq]
        · intro j hkj hj hnz
          have hnz' := (RestrictionBridge.nontrivial_generalLinearDerivative_iff
            T ψ (a := N + 1) (n := N) rfl hj (by omega) d.induced).mpr hnz
          let := hcalc.1 j hj hkj
          obtain ⟨x, y, hxy⟩ := hnz'.exists_pair_ne
          exact hxy (Subsingleton.elim x y)
      apply generalLinear_stronglyIndecomposable_of_highestDerivative.{uF, max uF uV}
        F T ψ N k hk' d.induced
        (segmentSocleProduct_nontrivial.{uF, uV} F T d hs) hlevel.symm
        (segmentSocleProductHomogeneity.{uF, max uF uV} F T ψ N d hs
          (precedenceOrdered_endpointSeparated.{uF, max uF uV} F T hfree d.segments ho))
      rwa [← hderivEq]

/-- Every actual nonprecedence-ordered product of supplied segment socles has
an irreducible socle, unique as an actual subobject. -/
theorem orderedMultisegmentSocleExistence :
    OrderedMultisegmentSocleExistence.{uF, uV} F T := by
  let := T.topology
  intro n d ho hs
  cases n with
  | zero =>
    exact ⟨d.induced, orderedMultisegmentSocle_rankZero.{uF, uV} F T d ho hs⟩
  | succ N =>
    obtain ⟨ψ⟩ := HarmonicAnalysis.padicUnitaryAdditiveCharacterExists F T
    exact segmentProduct_socle_of_stronglyIndecomposable_pos.{uF, uV} F T
      (Nat.zero_lt_succ N) d ho hs
      (segmentSocleProduct_nontrivial.{uF, uV} F T d hs)
      (orderedSegmentProduct_stronglyIndecomposable.{uF, uV} F T ψ (N + 1) d ho hs)

end Langlands.Classification
