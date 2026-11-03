import Langlands.Representation.Classification.SegmentProductDerivativeConstituentSupport
import Langlands.Representation.Classification.NonjuxtaposedSegmentSupport
import Langlands.Representation.Classification.CuspidalIntegralTwistFreenessProof
import Langlands.Representation.Classification.HighestDerivativeSupportShiftProof
import Langlands.Representation.Category.RenardFinitenessProof
import Langlands.Representation.Smooth.RenardIrreducibleExistenceProof
import Langlands.Representation.Filtration.ExactSmoothSubquotients

/-! The constituent level of a product with no juxtaposed segment positions. -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace Langlands.Classification

open GeneralLinear PadicField.TopologicalData Derivative

universe uF uV

namespace NonjuxtaposedConstituentLevel

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

private theorem residualContent_eq (Δ : T.Segment.{uV, uF}) (b : Bool) :
    SegmentSocleDerivativeConstituentSupport.residualContent T Δ b =
      NonjuxtaposedSegmentSupport.residualContent Δ b := by
  cases b with
  | false => rfl
  | true =>
    by_cases h : 2 ≤ Δ.length
    · simp [SegmentSocleDerivativeConstituentSupport.residualContent,
        NonjuxtaposedSegmentSupport.residualContent, SegmentContentShift.lower, h]
    · simp [SegmentSocleDerivativeConstituentSupport.residualContent,
        NonjuxtaposedSegmentSupport.residualContent, SegmentContentShift.lower, h]

private theorem fullContent_eq {n : ℕ} (d : T.SegmentProductDatum.{uV, uF} n) :
    d.multisegment.cuspidalContent = ∑ i, (d.segments i).cuspidalContent := by
  simp [SegmentProductDatum.multisegment, Multisegment.cuspidalContent,
    List.map_ofFn, List.sum_ofFn, Function.comp_def]

private theorem nontrivial_of_order_eq
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)
    {n a b : ℕ} (hab : a = b) (ha : a ≤ n) (hb : b ≤ n)
    (ω : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier))
    (h : Nontrivial ((generalLinearDerivative T ψ n a ha).obj ω)) :
    Nontrivial ((generalLinearDerivative T ψ n b hb).obj ω) := by
  cases hab
  exact h

end NonjuxtaposedConstituentLevel

/-- Zelevinsky Proposition 4.3: every irreducible constituent has level equal
to the sum of the segment ranks when distinct positions are not juxtaposed. -/
theorem nonjuxtaposedSegmentSocleConstituentLevel
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData) :
    NonjuxtaposedSegmentSocleConstituentLevel.{uF, uV} F T := by
  let := T.topology
  classical
  intro ψ n d hd hsep k hk hks ω hω hωd
  let P : ℕ → Prop := fun j => ∃ hj : j ≤ n,
    Nontrivial ((generalLinearDerivative T ψ n j hj).obj ω)
  have hP0 : P 0 := by
    refine ⟨Nat.zero_le _, ?_⟩
    change Nontrivial ω
    let := hω
    exact IsSimpleModule.nontrivial
      (MonoidAlgebra ℂ (GeneralLinear n F.Carrier)) ω.representation.asModule
  let m := Nat.findGreatest P n
  have hPm : P m := Nat.findGreatest_spec (Nat.zero_le n) hP0
  obtain ⟨hm, hnt⟩ := hPm
  have hhigh : ∀ (j : ℕ) (hj : j ≤ n), m < j →
      Subsingleton ((generalLinearDerivative T ψ n j hj).obj ω) := by
    intro j hj hmj
    rcases subsingleton_or_nontrivial
      ((generalLinearDerivative T ψ n j hj).obj ω) with hz | hn
    · exact hz
    · have hPj : P j := ⟨hj, hn⟩
      have hle : j ≤ m := Nat.le_findGreatest hj hPj
      omega
  let A := (generalLinearDerivative T ψ n m hm).obj ω
  let : Nontrivial A := hnt
  have hA : A.HasFiniteLength :=
    generalLinearDerivativeFiniteLength F T ψ n m hm ω
      (hasFiniteLength_of_isIrreducible hω)
  obtain ⟨σ, hσ, j, hj⟩ :=
    SmoothRep.RenardIrreducibleExistence.exists_irreducible_subrepresentation_of_finiteLength
      A ((SmoothRep.renardFiniteLength_iff A).mpr hA)
  have hσA : SmoothRep.IsSubquotient σ A :=
    SmoothRep.IsSubrepresentation.isSubquotient ⟨j, hj⟩
  have hAd := ExactSmoothTransport.map_isSubquotient
    (generalLinearDerivative T ψ n m hm)
    (generalLinearDerivativeExactness F T ψ n m hm) hωd
  have hσd := smoothSubquotientTransitivity ℂ _ _ _ _ hσA hAd
  obtain ⟨bs, horder, hsσ⟩ :=
    SegmentProductDerivativeConstituentSupport.product_support T ψ d hd m hm σ hσ hσd
  have hsω := SegmentSocleDerivativeConstituentSupport.support_of_product T d hd ω hω hωd
  have hshift := highestDerivativeSupportShift F T ψ n ω m hm hω hnt hhigh σ
    ⟨hσ, SmoothRep.hom j, hj⟩ _ _ hsω hsσ
  have hcontent :
      (∑ i : Fin d.length,
        SegmentSocleDerivativeConstituentSupport.residualContent T (d.segments i) (bs i)) =
        NonjuxtaposedSegmentSupport.content d.segments bs := by
    apply Finset.sum_congr rfl
    intro i _
    exact NonjuxtaposedConstituentLevel.residualContent_eq T _ _
  rw [hcontent, NonjuxtaposedConstituentLevel.fullContent_eq T d] at hshift
  have hmk : m = k := horder.trans
    ((NonjuxtaposedSegmentSupport.sum_orders_eq_sum_ranks
      (cuspidalIntegralTwistFreeness F T) d.segments bs hsep hshift).trans hks.symm)
  constructor
  · exact NonjuxtaposedConstituentLevel.nontrivial_of_order_eq T ψ hmk hm hk ω hnt
  · intro j hj hkj
    exact hhigh j hj (by omega)

end Langlands.Classification
