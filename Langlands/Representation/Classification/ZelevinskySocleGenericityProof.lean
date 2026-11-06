import Langlands.Representation.Classification.SegmentGenericStatement
import Langlands.Representation.Classification.SegmentSocleProductHighestDerivativeProof
import Langlands.Representation.Classification.SegmentSocleProductHomogeneityProof
import Langlands.Representation.Classification.OrderedMultisegmentSocleBoundaryProof
import Langlands.Representation.Classification.CuspidalIntegralTwistFreenessProof
import Langlands.Representation.Classification.SupercuspidalEmbeddingProof
import Langlands.Representation.Derivative.GeneralLinearDerivativeExactnessProof
import Langlands.Representation.Derivative.RestrictionBridge
import Langlands.Representation.Derivative.TopLocalizationComparison
import Langlands.Representation.Whittaker.LocalizationDual

/-! # Genericity of actual Zelevinsky socles -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.Classification

open CategoryTheory GeneralLinear PadicField.TopologicalData Derivative

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData)

private def rankCastLinearEquiv {a b : ℕ} (h : a = b)
    (X : letI := T.topology; SmoothRep.{0,uF,uV} ℂ (GeneralLinear a F.Carrier)) :
    letI := T.topology
    X ≃ₗ[ℂ] (generalLinearRankCast T h).obj X := by
  subst b
  exact LinearEquiv.refl ℂ X

private theorem functional_iff_top_nontrivial
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (n : ℕ) (π : letI := T.topology
      SmoothRep.{0,uF,uV} ℂ (GeneralLinear (n + 1) F.Carrier)) :
    letI := T.topology
    Whittaker.HasFunctional
      (N := upperUnipotent (n + 1) F.Carrier)
      (θ := Whittaker.standardCharacter ψ n) π.representation ↔
      Nontrivial ((generalLinearDerivative T ψ (n + 1) (n + 1) le_rfl).obj π) := by
  let := T.topology
  let U := upperUnipotent (n + 1) F.Carrier
  let θ := Whittaker.entrywiseCharacter ψ.complex (n + 1)
  let Q := Jacquet.Localization.Coinvariants π.representation U θ
  let f := Whittaker.functionalsLocalizationDualEquiv U θ π.representation
  let e := (SmoothRep.equivOfIso
    ((TopLocalization.topLocalizationIso T ψ (n + 1)).app π)).toLinearEquiv
  let r := rankCastLinearEquiv T (Nat.sub_self (n + 1))
    ((generalLinearDerivative T ψ (n + 1) (n + 1) le_rfl).obj π)
  have hf : Whittaker.HasFunctional (N := U) (θ := θ) π.representation ↔
      Nontrivial (Whittaker.functionals U θ π.representation) := by
    constructor
    · rintro ⟨ℓ, hℓ⟩
      exact nontrivial_of_ne ℓ 0 (fun h => hℓ (congrArg Subtype.val h))
    · intro h
      let := h
      obtain ⟨ℓ, hℓ⟩ := exists_ne (0 : Whittaker.functionals U θ π.representation)
      exact ⟨ℓ, fun hzero => hℓ (Subtype.ext hzero)⟩
  rw [← Whittaker.entrywiseCharacter_eq_standardCharacter]
  change Whittaker.HasFunctional (N := U) (θ := θ) π.representation ↔ _
  exact hf.trans ((Equiv.nontrivial_congr f.toEquiv).trans
    ((Module.nontrivial_dual_iff ℂ).trans
      ((Equiv.nontrivial_congr e.toEquiv).trans
        (Equiv.nontrivial_congr r.toEquiv).symm)))

private theorem rank_le_degree (Δ : T.Segment.{uV,uF}) : Δ.rank ≤ Δ.degree := by
  simpa using Nat.mul_le_mul_right Δ.rank Δ.length_pos

private theorem rank_sum_le {n : ℕ} (d : T.SegmentProductDatum.{uV,uF} n) :
    (∑ i, (d.segments i).rank) ≤ n := by
  calc
    (∑ i, (d.segments i).rank) ≤ ∑ i, (d.segments i).degree :=
      Finset.sum_le_sum (fun i _ => rank_le_degree T (d.segments i))
    _ = n := d.degree_sum

private theorem subrepresentation_generic_iff
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (n : ℕ) (d : T.SegmentProductDatum.{uV,uF} (n + 1))
    (π : letI := T.topology
      SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear (n + 1) F.Carrier))
    (hπ : d.IsZelevinskySubrepresentation π) :
    letI := T.topology
    Whittaker.IsGeneric ψ n π.representation ↔ ∀ i, (d.segments i).length = 1 := by
  classical
  let := T.topology
  obtain ⟨ho, hs, hirr, j, hj⟩ := hπ
  let jS : π ⟶ d.induced := SmoothRep.ofHom j
  have hjS : Function.Injective (SmoothRep.hom jS) := hj
  have hk := rank_sum_le T d
  have hcalc := segmentSocleProductHighestDerivative.{uF,uV} F T ψ (n + 1) d hs _ hk rfl
  constructor
  · intro hg i
    by_contra hlen
    have hlt : (∑ i, (d.segments i).rank) < n + 1 := by
      calc
        (∑ i, (d.segments i).rank) < ∑ i, (d.segments i).degree := by
          apply Finset.sum_lt_sum (fun i _ => rank_le_degree T (d.segments i))
          refine ⟨i, Finset.mem_univ i, ?_⟩
          have hp := (d.segments i).rank_pos
          have hl := (d.segments i).length_pos
          change (d.segments i).rank < (d.segments i).length * (d.segments i).rank
          simpa only [Nat.one_mul] using Nat.mul_lt_mul_of_pos_right
            (by omega : 1 < (d.segments i).length) hp
        _ = n + 1 := d.degree_sum
    let D := generalLinearDerivative.{uF,max uF uV} T ψ (n + 1) (n + 1) le_rfl
    have hDj : Function.Injective (SmoothRep.hom (D.map jS)) :=
      LevelCalculus.map_injective_of_exact
        (generalLinearDerivativeExactness.{uF,max uF uV} F T ψ (n + 1) (n + 1) le_rfl)
        jS hjS
    let : Subsingleton (D.obj d.induced) := hcalc.1 (n + 1) le_rfl hlt
    have hz : Subsingleton (D.obj π) := hDj.subsingleton
    exact (not_nontrivial_iff_subsingleton.mpr hz)
      ((functional_iff_top_nontrivial T ψ n π).mp hg.2.2)
  · intro hall
    have hsum : n + 1 = ∑ i, (d.segments i).rank := by
      calc
        n + 1 = ∑ i, (d.segments i).degree := d.degree_sum.symm
        _ = ∑ i, (d.segments i).rank := by
          apply Finset.sum_congr rfl
          intro i _
          simp only [Segment.degree, hall i, Nat.one_mul]
    have hfin := (segmentSocleProductHighestDerivative.{uF,uV} F T ψ (n + 1) d hs
      (n + 1) le_rfl hsum).2.2 hall
    have hnt : Nontrivial
        ((generalLinearDerivative.{uF,max uF uV} T ψ (n + 1) (n + 1) le_rfl).obj d.induced) :=
      Module.nontrivial_of_finrank_eq_succ hfin
    have hsep := precedenceOrdered_endpointSeparated.{uF,uV} F T
      (cuspidalIntegralTwistFreeness.{uF,uV} F T) d.segments ho
    have hhom : IsHomogeneous T ψ ((generalLinearRestriction T n).obj d.induced) :=
      (isGeneralLinearHomogeneous_iff T ψ d.induced).mp
        (segmentSocleProductHomogeneity.{uF,uV} F T ψ n d hs hsep)
    have hlevX : level T ψ ((generalLinearRestriction T n).obj d.induced) = n + 1 := by
      apply (level_eq_iff T ψ (Nat.succ_pos n) _).mpr
      refine ⟨le_rfl, ?_, ?_⟩
      · exact (RestrictionBridge.nontrivial_generalLinearDerivative_iff T ψ rfl le_rfl
          (Nat.succ_pos n) d.induced).mp hnt
      · intro m hlt hm
        omega
    have hjR : Function.Injective (SmoothRep.hom ((generalLinearRestriction T n).map jS)) :=
      LevelCalculus.map_injective_of_exact (generalLinearRestriction_mapsShortExact F T n)
        jS hjS
    have hπnt : Nontrivial π := by
      let := hirr
      exact IsSimpleModule.nontrivial (MonoidAlgebra ℂ (GeneralLinear (n + 1) F.Carrier))
        π.representation.asModule
    have hπR : Nontrivial ((generalLinearRestriction T n).obj π) := hπnt
    have hlev := LevelCalculus.level_eq_of_isHomogeneous T ψ hhom _ hjR hπR
    have hπtop := ((level_eq_iff T ψ (Nat.succ_pos n) _).mp (hlev.trans hlevX)).2.1
    have hntπ := (RestrictionBridge.nontrivial_generalLinearDerivative_iff T ψ rfl le_rfl
      (Nat.succ_pos n) π).mpr hπtop
    exact ⟨hirr, (CuspidalSupport.cuspidalEmbedding F T (n + 1) π hirr).1,
      (functional_iff_top_nontrivial T ψ n π).mpr hntπ⟩

/-- A supplied actual Zelevinsky socle is generic precisely when every segment
in its label is a singleton. -/
theorem zelevinskySocleGenericity (F : PadicField.{uF} p) (T : F.TopologicalData) :
    ZelevinskySocleGenericity.{uF,uV} F T := by
  let := T.topology
  intro ψ n a π ha
  obtain ⟨d, rfl, hd⟩ := ha
  rw [subrepresentation_generic_iff T ψ n d π hd.isZelevinskySubrepresentation]
  constructor
  · intro hall Δ hΔ
    obtain ⟨i, rfl⟩ : ∃ i, d.segments i = Δ := by
      simpa only [SegmentProductDatum.multisegment, Multiset.mem_coe, List.mem_ofFn] using hΔ
    exact hall i
  · intro hall i
    exact hall (d.segments i) (by
      simp only [SegmentProductDatum.multisegment, Multiset.mem_coe, List.mem_ofFn]
      exact ⟨i, rfl⟩)

end Langlands.Classification
