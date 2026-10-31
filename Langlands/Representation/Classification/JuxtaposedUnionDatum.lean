import Langlands.Representation.Classification.SegmentConstituentStatement
import Langlands.Representation.Classification.SegmentProductReplacement
import Langlands.Representation.Classification.CuspidalIntegralTwistFreenessProof
import Langlands.Representation.Induction.SingleBlock
import Langlands.Weil.Representation.IsomorphismInvarianceProof

/-! Actual union segments and one-block data for a juxtaposed pair. -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.PadicField.TopologicalData

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} {T : F.TopologicalData}

namespace Segment

/-- The concatenation starting at the earlier base, with both lengths retained. -/
def juxtaposedUnion (Δ Γ : Segment.{uV, uF} T) : Segment.{uV, uF} T where
  base := Δ.base
  length := Δ.length + Γ.length
  length_pos := by have := Δ.length_pos; omega

@[simp] theorem juxtaposedUnion_base (Δ Γ : Segment.{uV, uF} T) :
    (Δ.juxtaposedUnion Γ).base = Δ.base := rfl

@[simp] theorem juxtaposedUnion_length (Δ Γ : Segment.{uV, uF} T) :
    (Δ.juxtaposedUnion Γ).length = Δ.length + Γ.length := rfl

/-- Disjointness forces the beginning of the second interval to follow the first. -/
theorem IsJuxtaposed.base_eq_twist_length_of_precedes
    {Δ Γ : Segment.{uV, uF} T} (hj : Δ.IsJuxtaposed Γ) (hp : Δ.Precedes Γ) :
    Γ.base = Δ.base.twist (Δ.length : ℝ) := by
  have hfree := Classification.cuspidalIntegralTwistFreeness.{uF,uV} F T
  have hΔ := Δ.hasIntegralCoordinates_self
  obtain ⟨c, d, hΓ⟩ := hΔ.of_precedes_right hp
  obtain ⟨hac, hcb, hbd⟩ := hΔ.intervalPrecedes_of_precedes hfree hΓ hp
  have hc : c = (Δ.length : ℤ) := by
    have hsep : (Δ.length : ℤ) ≤ c := by
      by_contra hn
      have hmΔ : Δ.base.twist (c : ℝ) ∈ Δ.support :=
        (hΔ.twist_mem_support_iff hfree).mpr ⟨by omega, by omega⟩
      have hmΓ : Δ.base.twist (c : ℝ) ∈ Γ.support :=
        (hΓ.twist_mem_support_iff hfree).mpr ⟨le_refl _, hΓ.lower_le_upper⟩
      exact Set.disjoint_left.mp hj.2 hmΔ hmΓ
    omega
  simpa only [hc, Int.cast_natCast] using hΓ.1

/-- The explicit concatenation is the actual union, with empty intersection. -/
theorem IsJuxtaposed.union_replacement
    {Δ Γ : Segment.{uV, uF} T} (hj : Δ.IsJuxtaposed Γ) (hp : Δ.Precedes Γ) :
    IsUnionIntersectionReplacement Γ Δ (Δ.juxtaposedUnion Γ) none := by
  have hfree := Classification.cuspidalIntegralTwistFreeness.{uF,uV} F T
  have hΔ := Δ.hasIntegralCoordinates_self
  have hΓ : Γ.HasIntegralCoordinates Δ.base (Δ.length : ℤ)
      ((Δ.length : ℤ) + Γ.length - 1) :=
    ⟨by simpa only [Int.cast_natCast] using hj.base_eq_twist_length_of_precedes hp, rfl⟩
  have hU : (Δ.juxtaposedUnion Γ).HasIntegralCoordinates Δ.base 0
      ((Δ.length : ℤ) + Γ.length - 1) := by
    simp [HasIntegralCoordinates, juxtaposedUnion]
  have hle : (0 : ℤ) ≤ (Δ.length : ℤ) + Γ.length - 1 := by
    have := Δ.length_pos
    have := Γ.length_pos
    omega
  have hsupport : (Δ.juxtaposedUnion Γ).support = Δ.support ∪ Γ.support := by
    exact ((hU.support_eq_iff hfree
      (ofIntegralInterval_hasIntegralCoordinates Δ.base 0 _ hle)).mpr ⟨rfl, rfl⟩).trans
      (hΔ.support_union_eq hΓ (by omega) (by omega) (by have := Γ.length_pos; omega))
  exact ⟨hsupport.trans (Set.union_comm _ _),
    Set.disjoint_iff_inter_eq_empty.mp hj.2.symm⟩

/-- The explicit union retains the sum of the two general-linear degrees. -/
theorem IsJuxtaposed.union_degree
    {Δ Γ : Segment.{uV, uF} T} (hj : Δ.IsJuxtaposed Γ) (hp : Δ.Precedes Γ) :
    (Δ.juxtaposedUnion Γ).degree = Δ.degree + Γ.degree := by
  have hr : Γ.rank = Δ.rank := by
    simp only [rank, hj.base_eq_twist_length_of_precedes hp, CuspidalDatum.twist_rank]
  simp only [degree, juxtaposedUnion_length, rank, juxtaposedUnion_base] at hr ⊢
  rw [hr, Nat.add_mul]

end Segment

namespace SegmentProductDatum

/-- Actual one-block datum at a certified total degree. -/
def ofSingleSegment {n : ℕ} (U : Segment.{uV, uF} T)
    (π : letI := T.topology
      SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear U.degree F.Carrier))
    (hdegree : U.degree = n) : SegmentProductDatum.{uV,uF} T n :=
  ofBlockList [⟨U, π⟩] (by simpa using hdegree)

@[simp] theorem ofSingleSegment_length {n : ℕ} (U : Segment.{uV,uF} T)
    (π : letI := T.topology
      SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear U.degree F.Carrier))
    (hdegree : U.degree = n) : (ofSingleSegment U π hdegree).length = 1 := rfl

@[simp] theorem ofSingleSegment_segments {n : ℕ} (U : Segment.{uV,uF} T)
    (π : letI := T.topology
      SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear U.degree F.Carrier))
    (hdegree : U.degree = n) : List.ofFn (ofSingleSegment U π hdegree).segments = [U] := by
  simp [ofSingleSegment]

@[simp] theorem ofSingleSegment_segment {n : ℕ} (U : Segment.{uV,uF} T)
    (π : letI := T.topology
      SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear U.degree F.Carrier))
    (hdegree : U.degree = n) : (ofSingleSegment U π hdegree).segments ⟨0, by rw [ofSingleSegment_length]; omega⟩ = U := rfl

/-- Supplied strong segment-socle evidence is retained by the datum. -/
theorem ofSingleSegment_hasSegmentSocles {n : ℕ} (U : Segment.{uV,uF} T)
    (π : letI := T.topology
      SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear U.degree F.Carrier))
    (hdegree : U.degree = n) (hπ : T.IsSegmentSocle U π) :
    (ofSingleSegment U π hdegree).HasSegmentSocles := by
  apply (ofBlockList_hasSegmentSocles_iff _ _).mpr
  simpa [SegmentBlock.IsSocle] using hπ

/-- The induced representation is the supplied sole factor after exact rank transport. -/
def ofSingleSegmentInducedEquiv {n : ℕ} (U : Segment.{uV,uF} T)
    (π : letI := T.topology
      SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear U.degree F.Carrier))
    (hdegree : U.degree = n) : letI := T.topology
    (ofSingleSegment U π hdegree).induced.representation.Equiv
      (hdegree ▸ π).representation := by
  subst n
  letI := T.topology
  let e := ofSingleSegment U π rfl
  let E := T.singleBlockNormalizedProductEquiv e.shape rfl
    (fun i => (e.blocks i).representation) (fun i => (e.blocks i).isSmooth)
    ⟨0, by change 0 < 1; omega⟩
  refine E.trans (Representation.Equiv.mk (LinearEquiv.refl ℂ π) ?_)
  intro g
  have hg : (GeneralLinear.reindex (R := F.Carrier)
      (finCongr (rfl : U.degree = U.degree))).symm g = g := by
    apply Units.ext
    ext a b
    rfl
  change π.representation ((GeneralLinear.reindex (R := F.Carrier)
    (finCongr (rfl : U.degree = U.degree))).symm g) = π.representation g
  rw [hg]

/-- The induced one-block datum is irreducible if its supplied factor is. -/
theorem ofSingleSegment_induced_irreducible {n : ℕ} (U : Segment.{uV,uF} T)
    (π : letI := T.topology
      SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear U.degree F.Carrier))
    (hdegree : U.degree = n) (hπ : letI := T.topology; π.IsIrreducible) :
    letI := T.topology
    Representation.IsIrreducible (ofSingleSegment U π hdegree).induced.representation := by
  subst n
  let := T.topology
  exact (Weil.IsomorphismInvariance.irreducible_iff
    (ofSingleSegmentInducedEquiv U π rfl)).mpr hπ

end SegmentProductDatum

/-- A juxtaposed pair admits actual union-socle data, conditional only on the
existing individual-segment existence proposition. No product-socle assertion is used. -/
theorem exists_juxtaposedUnionDatum
    (hex : Classification.SegmentZelevinskyConstituentExistence.{uF,uV} F T)
    {n : ℕ} (d : SegmentProductDatum.{uV,uF} T n) (h₂ : d.length = 2)
    (hp : (d.segments ⟨1, by omega⟩).Precedes (d.segments ⟨0, by omega⟩))
    (hj : (d.segments ⟨1, by omega⟩).IsJuxtaposed (d.segments ⟨0, by omega⟩)) :
    letI := T.topology
    ∃ (U : Segment.{uV,uF} T) (e : SegmentProductDatum.{uV,uF} T n),
      (d.segments ⟨0, by omega⟩).IsUnionIntersectionReplacement
        (d.segments ⟨1, by omega⟩) U none ∧
      List.ofFn e.segments = [U] ∧ e.HasSegmentSocles ∧
      Representation.IsIrreducible e.induced.representation ∧
      U.base = (d.segments ⟨1, by omega⟩).base ∧
      U.length = (d.segments ⟨1, by omega⟩).length + (d.segments ⟨0, by omega⟩).length ∧
      U.degree = n ∧ e.length = 1 ∧ ∀ i, e.segments i = U := by
  let := T.topology
  let Δ := d.segments ⟨1, by omega⟩
  let Γ := d.segments ⟨0, by omega⟩
  let U := Δ.juxtaposedUnion Γ
  have hsum : Γ.degree + Δ.degree = n := by
    change (d.segments ⟨0, by omega⟩).degree + (d.segments ⟨1, by omega⟩).degree = n
    rcases d with ⟨l, segments, hsum, blocks⟩
    dsimp only at h₂
    subst l
    simpa [Fin.sum_univ_two] using hsum
  have hdegree : U.degree = n := by
    calc U.degree = Δ.degree + Γ.degree := hj.union_degree hp
         _ = n := (Nat.add_comm _ _).trans hsum
  obtain ⟨π, hπ, _⟩ := hex U
  have hirr : π.IsIrreducible := by
    obtain ⟨A, hA, hπ'⟩ := hπ
    exact hπ'.1
  refine ⟨U, SegmentProductDatum.ofSingleSegment U π hdegree,
    hj.union_replacement hp, SegmentProductDatum.ofSingleSegment_segments U π hdegree,
    SegmentProductDatum.ofSingleSegment_hasSegmentSocles U π hdegree hπ,
    SegmentProductDatum.ofSingleSegment_induced_irreducible U π hdegree hirr,
    rfl, rfl, hdegree, rfl, ?_⟩
  intro i
  have hi : i = ⟨0, by change 0 < 1; omega⟩ := by
    apply Fin.ext
    change i.val = 0
    have := i.isLt
    change i.val < 1 at this
    omega
  subst i
  rfl

end Langlands.PadicField.TopologicalData
