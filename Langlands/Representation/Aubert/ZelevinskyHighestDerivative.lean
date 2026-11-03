import Langlands.Representation.Aubert.SegmentProductClass
import Langlands.Representation.Aubert.MultisegmentRankOrder
import Langlands.Representation.Classification.SegmentSocleProductHomogeneityStatement
import Langlands.Representation.Classification.SegmentSocleProductHighestDerivativeProof
import Langlands.Representation.Classification.OrderedMultisegmentSocleBoundaryProof
import Langlands.Representation.Classification.SegmentInitialTruncationOrderProof
import Langlands.Representation.Classification.CuspidalIntegralTwistFreenessProof
import Langlands.Representation.Classification.SegmentHeadSupportStep
import Langlands.Representation.Derivative.LevelCalculus
import Langlands.Representation.Derivative.RankCastCompat
import Langlands.Representation.Derivative.GeneralLinearDerivativeExactnessProof

/-!
# A label of the highest derivative of a Zelevinsky subrepresentation

Let `π` be an irreducible subrepresentation of a precedence-ordered product
`⟨Δ_1⟩ × ⋯ × ⟨Δ_r⟩` of supplied segment socles on `GL_n`, `n > 0`, and let
`λ = ∑ i, rank Δ_i`. Assuming the homogeneity statement of Zelevinsky 1980,
Theorem 6.2, for endpoint-separated segment-socle products, the order-`λ`
derivative of `π` has an irreducible subrepresentation `π'` that is itself an
irreducible subrepresentation of a precedence-ordered product of segment socles
with multisegment `a⁻ = {Δ_1⁻, …, Δ_r⁻}`. This is the weak-label form of
Zelevinsky 1980, Theorem 6.6, used for the surjectivity half of Corollary 7.5.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace Langlands.Aubert.ZelevinskyHighestDerivative

open PadicField.TopologicalData Classification Derivative

universe uF uV uG uW

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- The rank of a segment is at most its degree. -/
theorem rank_le_degree (Δ : T.Segment.{uV, uF}) : Δ.rank ≤ Δ.degree := by
  simpa using Nat.mul_le_mul_right Δ.rank Δ.length_pos

/-- The total rank `λ` of a segment-product datum is at most its degree. -/
theorem sum_rank_le {n : ℕ} (d : T.SegmentProductDatum.{uV, uF} n) :
    ∑ i, (d.segments i).rank ≤ n :=
  calc
    ∑ i, (d.segments i).rank ≤ ∑ i, (d.segments i).degree :=
      Finset.sum_le_sum fun i _ => rank_le_degree F T (d.segments i)
    _ = n := d.degree_sum

/-- In positive degree the total rank `λ` is positive. -/
theorem sum_rank_pos {n : ℕ} (hn : 0 < n) (d : T.SegmentProductDatum.{uV, uF} n) :
    0 < ∑ i, (d.segments i).rank := by
  have hne : Nonempty (Fin d.length) := by
    by_contra h
    rw [not_nonempty_iff] at h
    have hsum := d.degree_sum
    rw [Finset.univ_eq_empty, Finset.sum_empty] at hsum
    omega
  exact Finset.sum_pos (fun i _ => (d.segments i).rank_pos) Finset.univ_nonempty

/-- The list operation in the highest-derivative theorem is `dropLastList`. -/
theorem filterMap_eq_dropLastList (l : List T.Segment.{uV, uF}) :
    l.filterMap (fun Δ => if h : 2 ≤ Δ.length then
        some (⟨Δ.base, Δ.length - 1, by omega⟩ : T.Segment.{uV, uF}) else none) =
      Segment.dropLastList l := by
  unfold Segment.dropLastList
  congr 1

/-- A positive-order derivative of the mirabolic restriction is nonzero exactly
when the general-linear derivative of the same order is nonzero. -/
theorem hasNonzeroDerivative_restriction_iff
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)
    {N k : ℕ} (hk : 0 < k ∧ k ≤ N + 1) :
    letI := T.topology
    ∀ X : SmoothRep.{0, uF, uV} ℂ (GeneralLinear (N + 1) F.Carrier),
      HasNonzeroDerivative T ψ ((generalLinearRestriction T N).obj X) k ↔
        Nontrivial ((generalLinearDerivative.{uF, uV} T ψ (N + 1) k hk.2).obj X) := by
  let _ := T.topology
  intro X
  exact (hasNonzeroDerivative_iff T ψ hk _).trans
    (LevelCalculus.nontrivial_iff_of_iso
      ((generalLinearRestrictionDerivativeIso T ψ N k hk).app X))

/-- An injective morphism of smooth representations transfers finite length
from its target to its source. -/
theorem hasFiniteLength_of_injective {G : Type uG} [Group G] [TopologicalSpace G]
    {A B : SmoothRep.{0, uG, uW} ℂ G} (f : A ⟶ B) (hf : Function.Injective (SmoothRep.hom f))
    (hB : B.HasFiniteLength) : A.HasFiniteLength :=
  IsFiniteLength.of_injective hB
    (f := Representation.IntertwiningMap.equivLinearMapAsModule _ _ (SmoothRep.hom f)) hf

/-- Weak-label form of Zelevinsky 1980, Theorem 6.6, from the homogeneity
statement of Theorem 6.2: the order-`λ` derivative of an irreducible
subrepresentation of a precedence-ordered segment-socle product has an
irreducible subquotient that is a Zelevinsky subrepresentation for `a⁻`. -/
theorem exists_label_subquotient
    (hH : Classification.SegmentSocleProductHomogeneity.{uF, max uF uV} F T)
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology) :
    letI := T.topology
    ∀ (n : ℕ), 0 < n → ∀ (d : T.SegmentProductDatum.{max uF uV, uF} n)
      (π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)),
      d.IsZelevinskySubrepresentation π →
        ∃ (hk : ∑ i, (d.segments i).rank ≤ n)
          (d' : T.SegmentProductDatum.{max uF uV, uF} (n - ∑ i, (d.segments i).rank))
          (π' : SmoothRep.{0, uF, max uF uV} ℂ
            (GeneralLinear (n - ∑ i, (d.segments i).rank) F.Carrier)),
          d'.multisegment = d.multisegment.dropLast ∧
          d'.IsZelevinskySubrepresentation π' ∧
          SmoothRep.IsSubquotient π'
            ((Derivative.generalLinearDerivative.{uF, max uF uV} T ψ n
              (∑ i, (d.segments i).rank) hk).obj π) := by
  let _ := T.topology
  intro n hn d π hπ
  obtain ⟨ho, hs, hirr, j, hj⟩ := hπ
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 1 := ⟨n - 1, by omega⟩
  have hk : ∑ i, (d.segments i).rank ≤ N + 1 := sum_rank_le F T d
  have hkpos : 0 < ∑ i, (d.segments i).rank := sum_rank_pos F T hn d
  have hk' : 0 < ∑ i, (d.segments i).rank ∧ ∑ i, (d.segments i).rank ≤ N + 1 :=
    ⟨hkpos, hk⟩
  -- The highest derivative of the product (Ze80 Thm 6.6 for the product itself).
  obtain ⟨hvan, ⟨d', hlist, hs', ⟨e⟩⟩, -⟩ :=
    segmentSocleProductHighestDerivative.{uF, max uF uV} F T ψ (N + 1) d hs _ hk rfl
  have hlist' : List.ofFn d'.segments = Segment.dropLastList (List.ofFn d.segments) :=
    hlist.trans (filterMap_eq_dropLastList F T _)
  -- Homogeneity of the restricted product (Ze80 Thm 6.2).
  have hsep := precedenceOrdered_endpointSeparated.{uF, max uF uV} F T
    (cuspidalIntegralTwistFreeness.{uF, max uF uV} F T) d.segments ho
  have hhom : IsHomogeneous T ψ ((generalLinearRestriction T N).obj d.induced) :=
    (isGeneralLinearHomogeneous_iff T ψ d.induced).mp (hH ψ N d hs hsep)
  -- The level of the restricted product is `λ`.
  have hlevX : level T ψ ((generalLinearRestriction T N).obj d.induced) =
      ∑ i, (d.segments i).rank := by
    rw [level_eq_iff T ψ hkpos]
    refine ⟨hk, ?_, ?_⟩
    · rw [hasNonzeroDerivative_restriction_iff F T ψ hk', LevelCalculus.nontrivial_iff_of_iso e]
      exact segmentSocleProduct_nontrivial F T d' hs'
    · intro m hkm hm hnz
      rw [hasNonzeroDerivative_restriction_iff F T ψ ⟨by omega, hm⟩] at hnz
      exact (not_nontrivial_iff_subsingleton.mpr (hvan m hm hkm)) hnz
  -- Transport the level to the subrepresentation `π`.
  let jS : π ⟶ d.induced := SmoothRep.ofHom j
  have hjS : Function.Injective (SmoothRep.hom jS) := hj
  have hjR : Function.Injective (SmoothRep.hom ((generalLinearRestriction T N).map jS)) :=
    LevelCalculus.map_injective_of_exact (generalLinearRestriction_mapsShortExact F T N) jS hjS
  have hπnt : Nontrivial π := SegmentHeadSupport.nontrivial_of_isIrreducible hirr
  have hπR : Nontrivial ((generalLinearRestriction T N).obj π) := hπnt
  have hlev := LevelCalculus.level_eq_of_isHomogeneous T ψ hhom _ hjR hπR
  have hπk := ((level_eq_iff T ψ hkpos _).mp (hlev.trans hlevX)).2.1
  rw [hasNonzeroDerivative_restriction_iff F T ψ hk'] at hπk
  -- The order-`λ` derivative of `π` embeds into the product of the `⟨Δ_i⁻⟩`.
  let D := generalLinearDerivative.{uF, max uF uV} T ψ (N + 1) (∑ i, (d.segments i).rank) hk
  have hDj : Function.Injective (SmoothRep.hom (D.map jS)) :=
    LevelCalculus.map_injective_of_exact
      (generalLinearDerivativeExactness.{uF, max uF uV} F T ψ (N + 1) _ hk) jS hjS
  have hDe : Function.Injective (SmoothRep.hom (D.map jS ≫ e.hom)) :=
    (LevelCalculus.iso_hom_injective e).comp hDj
  have hFL : (D.obj π).HasFiniteLength :=
    hasFiniteLength_of_injective (D.map jS ≫ e.hom) hDe
      (SegmentProductClass.hasFiniteLength_induced F T d' hs')
  obtain ⟨C, hC, jC, hjC⟩ := SegmentHeadSupport.exists_irreducible_subrepresentation hFL
  refine ⟨hk, d', C, ?_, ⟨?_, hs', hC, SmoothRep.hom (jC ≫ D.map jS ≫ e.hom),
    hDe.comp hjC⟩, SmoothRep.IsSubrepresentation.isSubquotient ⟨jC, hjC⟩⟩
  · unfold SegmentProductDatum.multisegment
    rw [Multisegment.dropLast_coe, hlist']
  · have h₁ := (segmentInitialTruncationOrder.{uF, max uF uV} F T
      (cuspidalIntegralTwistFreeness.{uF, max uF uV} F T)).2 _
      ((T.isPrecedenceOrdered_iff_list d.segments).mp ho)
    rw [← hlist'] at h₁
    exact (T.isPrecedenceOrdered_iff_list d'.segments).mpr h₁

end Langlands.Aubert.ZelevinskyHighestDerivative
