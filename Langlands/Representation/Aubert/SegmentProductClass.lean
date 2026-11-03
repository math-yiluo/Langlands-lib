import Langlands.Representation.Aubert.ZelevinskyPolynomial
import Langlands.Representation.Aubert.GradedInductionCommutativityProof
import Langlands.Representation.Classification.SegmentProductOrderedAssembly
import Langlands.Representation.Classification.IrreducibleProductFiniteLengthProof

/-!
# The class of a product of segment socles

The graded exact-K0 class of the actual product `i(π_1, …, π_r)` of supplied
segment socles `π_i` of `Δ_1, …, Δ_r` is the value of the segment polynomial
evaluation at the monomial `X_{Δ_1} ⋯ X_{Δ_r}`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace Langlands.Aubert

open PadicField.TopologicalData Classification SmoothRep.FiniteLengthGrothendieckGroup

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)
  (hx : BinaryProductExactnessStatement.{uF, uV} F T)
  (hl : GradedInductionRingLawsStatement F T hx)

namespace SegmentProductClass

/-- Irreducibility is part of the supplied strong socle relation. -/
theorem isIrreducible_of_isSegmentSocle {Δ : T.Segment.{max uF uV, uF}}
    {π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier)}
    (hπ : T.IsSegmentSocle Δ π) :
    letI := T.topology
    π.IsIrreducible := by
  obtain ⟨_, _, h⟩ := hπ
  exact h.1

/-- A product of supplied segment socles has finite length in every rank,
including the empty product on `GL_0`. -/
theorem hasFiniteLength_induced {n : ℕ} (d : T.SegmentProductDatum.{max uF uV, uF} n)
    (hd : d.HasSegmentSocles) :
    letI := T.topology
    d.induced.HasFiniteLength := by
  let := T.topology
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact Derivative.ProductDerivativesFiniteLength.hasFiniteLength_of_iso
      (SegmentProductOrderedAssembly.zeroDatumUnitIso d).symm
      (binaryProductUnit_hasFiniteLength F T)
  · exact irreducibleProductFiniteLength.{uF, max uF uV} F T n hn d.shape d.blocks
      (fun i => isIrreducible_of_isSegmentSocle F T (hd i))

/-- A product over the segments of a datum with at least two segments splits
into its first factor and the product over the tail datum. -/
theorem prod_segments_eq_head_mul_tail {M : Type*} [CommMonoid M]
    (f : T.Segment.{max uF uV, uF} → M) {n k : ℕ}
    (d : T.SegmentProductDatum.{max uF uV, uF} n) (h : d.length = k + 2) :
    ∏ i, f (d.segments i) =
      f (d.segments (d.shape.headIndex h)) *
        ∏ j, f ((SegmentProductSplit.tail d h).segments j) := by
  rcases d with ⟨r, segments, hsum, blocks⟩
  dsimp at h
  subst r
  exact Fin.prod_univ_succ _

/-- The class of a supplied segment socle is the graded segment generator. -/
theorem gradedInclusion_eq_gradedSegmentSocle (Δ : T.Segment.{max uF uV, uF})
    (π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier))
    (hπ : letI := T.topology; π.HasFiniteLength) (hs : T.IsSegmentSocle Δ π) :
    letI := T.topology
    gradedInclusion F T Δ.degree (ofRepresentation π hπ) = gradedSegmentSocle F T Δ := by
  let := T.topology
  unfold gradedSegmentSocle
  rw [segmentSocleClass_of_object F T Δ π hπ hs]
  rfl

/-- The formula for data with a positive number `k + 1` of segments. -/
theorem gradedInclusion_induced_eq_prod_of_length_eq_succ (k : ℕ) :
    letI := T.topology
    letI := gradedInductionRing F T hx hl
    ∀ {n : ℕ} (d : T.SegmentProductDatum.{max uF uV, uF} n), d.length = k + 1 →
      d.HasSegmentSocles → ∀ hfin : d.induced.HasFiniteLength,
        gradedInclusion F T n (GeneralLinear.finiteLengthClass n F.Carrier d.induced hfin) =
          ∏ i, gradedSegmentSocle F T (d.segments i) := by
  let := T.topology
  let := gradedInductionRing F T hx hl
  induction k with
  | zero =>
    intro n d h hd hfin
    let i : Fin d.length := Fin.cast h.symm 0
    have hsz := d.shape.singleBlock_size h i
    have hb : (d.blocks i).HasFiniteLength :=
      SmoothRep.hasFiniteLength_of_isIrreducible (isIrreducible_of_isSegmentSocle F T (hd i))
    have : Subsingleton (Fin d.length) :=
      ⟨fun a b => Fin.ext (by have := a.isLt; have := b.isLt; omega)⟩
    calc gradedInclusion F T n (GeneralLinear.finiteLengthClass n F.Carrier d.induced hfin)
        = gradedInclusion F T n
            (ofRepresentation ((Derivative.generalLinearRankCast T hsz).obj (d.blocks i))
              (Derivative.ProductDerivativesFiniteLength.hasFiniteLength_rankCast T hsz _ hb)) :=
          congrArg (gradedInclusion F T n)
            (ofObject_eq_of_iso (SegmentProductOrderedAssembly.singletonIso d h i))
      _ = gradedInclusion F T (d.segments i).degree (ofRepresentation (d.blocks i) hb) :=
          gradedInclusion_rankCast F T hsz _ hb
      _ = gradedSegmentSocle F T (d.segments i) :=
          gradedInclusion_eq_gradedSegmentSocle F T _ _ hb (hd i)
      _ = ∏ j, gradedSegmentSocle F T (d.segments j) :=
          (Fintype.prod_subsingleton (fun j => gradedSegmentSocle F T (d.segments j)) i).symm
  | succ k ih =>
    intro n d h' hd hfin
    have h : d.length = k + 2 := h'
    obtain ⟨e⟩ := SegmentProductSplit.nonempty_iso_binary d h
    let tl := SegmentProductSplit.tail d h
    have hab := d.shape.headRank_add_tailRank h
    have hA : (d.blocks (d.shape.headIndex h)).HasFiniteLength :=
      SmoothRep.hasFiniteLength_of_isIrreducible (isIrreducible_of_isSegmentSocle F T (hd _))
    have hB : tl.induced.HasFiniteLength :=
      hasFiniteLength_induced F T tl (SegmentProductSplit.tail_hasSegmentSocles d h hd)
    have hP := binaryProduct_preservesFiniteLength F T (d.shape.headRank h) (d.shape.tailRank h)
      _ _ hA hB
    calc gradedInclusion F T n (GeneralLinear.finiteLengthClass n F.Carrier d.induced hfin)
        = gradedInclusion F T n
            (ofRepresentation ((Derivative.generalLinearRankCast T hab).obj
              ((T.binaryNormalizedProductFunctor.{uF, max uF uV} (d.shape.headRank h)
                (d.shape.tailRank h)).obj (d.blocks (d.shape.headIndex h), tl.induced)))
              (Derivative.ProductDerivativesFiniteLength.hasFiniteLength_rankCast T hab _ hP)) :=
          congrArg (gradedInclusion F T n) (ofObject_eq_of_iso e)
      _ = gradedInclusion F T (d.shape.headRank h + d.shape.tailRank h)
            (ofRepresentation ((T.binaryNormalizedProductFunctor.{uF, max uF uV}
              (d.shape.headRank h) (d.shape.tailRank h)).obj
                (d.blocks (d.shape.headIndex h), tl.induced)) hP) :=
          gradedInclusion_rankCast F T hab _ hP
      _ = gradedInclusion F T (d.shape.headRank h + d.shape.tailRank h)
            (binaryProductK0 F T hx (d.shape.headRank h) (d.shape.tailRank h)
              (ofObject ⟨d.blocks (d.shape.headIndex h), hA⟩) (ofObject ⟨tl.induced, hB⟩)) := by
          rw [binaryProductK0_classes]
      _ = gradedInclusion F T (d.shape.headRank h) (ofRepresentation _ hA) *
            gradedInclusion F T (d.shape.tailRank h) (ofRepresentation _ hB) :=
          (gradedMultiplication_homogeneous F T hx _ _ _ _).symm
      _ = gradedSegmentSocle F T (d.segments (d.shape.headIndex h)) *
            ∏ j, gradedSegmentSocle F T (tl.segments j) := by
          exact congrArg₂ (· * ·) (gradedInclusion_eq_gradedSegmentSocle F T _ _ hA (hd _))
            (ih tl rfl (SegmentProductSplit.tail_hasSegmentSocles d h hd) hB)
      _ = ∏ i, gradedSegmentSocle F T (d.segments i) :=
          (prod_segments_eq_head_mul_tail F T _ d h).symm

end SegmentProductClass

open SegmentProductClass in
/-- **The class of a product of segment socles.** For a segment-product datum
`d` whose blocks are supplied segment socles, the graded class of the actual
product `d.induced` is the segment polynomial evaluation of the monomial
`∏ i, X (d.segments i)`. -/
theorem gradedInclusion_induced_eq_segmentPolynomialEvaluation
    {n : ℕ} (d : T.SegmentProductDatum.{max uF uV, uF} n) (hd : d.HasSegmentSocles)
    (hfin : letI := T.topology; d.induced.HasFiniteLength) :
    letI := T.topology
    gradedInclusion F T n (GeneralLinear.finiteLengthClass n F.Carrier d.induced hfin) =
      segmentPolynomialEvaluation F T hx hl (∏ i, MvPolynomial.X (d.segments i)) := by
  let := T.topology
  let := gradedInductionRing F T hx hl
  have hX : ∀ Δ : T.Segment.{max uF uV, uF},
      segmentPolynomialEvaluation F T hx hl (MvPolynomial.X Δ) = gradedSegmentSocle F T Δ :=
    fun Δ => MvPolynomial.eval₂Hom_X' _ _ _
  rw [map_prod]
  simp only [hX]
  by_cases hk : d.length = 0
  · have : IsEmpty (Fin d.length) := by rw [hk]; infer_instance
    have hn : n = 0 := by
      rw [← d.degree_sum]
      simp
    subst hn
    rw [Finset.univ_eq_empty, Finset.prod_empty]
    change _ = gradedUnit F T
    exact congrArg (gradedInclusion F T 0)
      (ofObject_eq_of_iso (SegmentProductOrderedAssembly.zeroDatumUnitIso d))
  · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hk
    exact gradedInclusion_induced_eq_prod_of_length_eq_succ F T hx hl k d hk hd hfin

end Langlands.Aubert
