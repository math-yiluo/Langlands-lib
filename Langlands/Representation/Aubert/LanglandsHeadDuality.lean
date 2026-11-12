import Langlands.Representation.Aubert.SegmentPolynomialSurjectivity
import Langlands.Representation.Aubert.AdjustedHomogeneousMultiplicativityProof
import Langlands.Representation.Aubert.AdjustedSegmentExchangeProof
import Langlands.Representation.Aubert.AdjustedInvolutivityProof
import Langlands.Representation.Aubert.BinaryProductExactnessProof
import Langlands.Representation.Aubert.GradedInductionRingLawsProof
import Langlands.Representation.Classification.MultisegmentSocleExhaustionProof
import Langlands.Representation.Classification.MultisegmentHeadClassificationProof
import Langlands.Representation.Classification.MultisegmentHeadExistenceProof
import Langlands.Representation.Classification.OrderedMultisegmentSocleExistenceProof

/-!
# Langlands heads as Aubert duals of Zelevinsky labels

The support-adjusted graded Aubert operator `t` sends the class of a Zelevinsky
label of a multisegment `a` to the class of every Langlands head of `a`. The proof
is a well-founded induction on the rank order of multisegments, using Zelevinsky's
triangularity, socle exhaustion and the multisegment head classification. The
K0 form of Zelevinsky 1980, Proposition 8.4, is proved for labels: the label of
`a + b` occurs in the product of the labels of `a` and `b`.
-/

noncomputable section

open CategoryTheory

namespace Langlands.Aubert

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

namespace LanglandsHeadDuality

open SegmentPolynomialSurjectivity PadicField.TopologicalData Classification
open SmoothRep SmoothRep.IrreducibleGrothendieckProof VirtualRepresentation
open SmoothRep.FiniteLengthGrothendieckGroup

/-! ### Coefficients -/

/-- Two functionals agreeing on every basis class occurring in `x` agree on `x`. -/
theorem apply_eq_of_basisClass {χ φ : GradedGrothendieckGroup.{uF, uV} F T →ₗ[ℤ] ℤ}
    {x : GradedGrothendieckGroup.{uF, uV} F T}
    (h : ∀ m c, coeff F T m c x ≠ 0 → χ (basisClass F T m c) = φ (basisClass F T m c)) :
    χ x = φ x := by
  classical
  let := T.topology
  rw [apply_eq_sum F T χ x, apply_eq_sum F T φ x]
  refine Finset.sum_congr rfl fun m _ => Finsupp.sum_congr fun c hc => ?_
  rw [h m c (Finsupp.mem_support_iff.mp hc)]

theorem basisClass_injective {m : ℕ} {c c' : Label.{uF, uV} F T m}
    (h : basisClass F T m c = basisClass F T m c') : c = c' := by
  by_contra hne
  have h1 := coeff_basisClass_self F T m c
  rw [h, coeff_basisClass_of_ne F T m (Ne.symm hne)] at h1
  exact zero_ne_one h1

/-! ### Products of effective classes -/

section Products

variable (hx : BinaryProductExactnessStatement.{uF, uV} F T)
  (hl : GradedInductionRingLawsStatement F T hx)

/-- The product of two actual finite-length classes is the class of their actual
normalized product. -/
theorem gradedInclusion_mul_gradedInclusion (m n : ℕ) :
    letI := T.topology
    letI := gradedInductionRing F T hx hl
    ∀ (A : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear m F.Carrier))
      (B : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier))
      (hA : A.HasFiniteLength) (hB : B.HasFiniteLength),
      gradedInclusion F T m (GeneralLinear.finiteLengthClass m F.Carrier A hA) *
          gradedInclusion F T n (GeneralLinear.finiteLengthClass n F.Carrier B hB) =
        gradedInclusion F T (m + n) (GeneralLinear.finiteLengthClass (m + n) F.Carrier
          ((T.binaryNormalizedProductFunctor.{uF, max uF uV} m n).obj (A, B))
          (binaryProduct_preservesFiniteLength F T m n _ _ hA hB)) := by
  let := T.topology
  let := gradedInductionRing F T hx hl
  intro A B hA hB
  exact (gradedMultiplication_homogeneous F T hx m n _ _).trans
    (congrArg (gradedInclusion F T (m + n)) (binaryProductK0_classes F T hx m n ⟨A, hA⟩ ⟨B, hB⟩))

theorem isEffective_basisClass_mul (m n : ℕ) (c : Label.{uF, uV} F T m)
    (c' : Label.{uF, uV} F T n) :
    letI := T.topology
    letI := gradedInductionRing F T hx hl
    IsEffective F T (basisClass F T m c * basisClass F T n c') := by
  let := T.topology
  let := gradedInductionRing F T hx hl
  obtain ⟨A, hA, rfl⟩ := IrreducibleIsoClass.exists_eq c
  obtain ⟨B, hB, rfl⟩ := IrreducibleIsoClass.exists_eq c'
  rw [basisClass_irreducibleIsoClass, basisClass_irreducibleIsoClass,
    gradedInclusion_mul_gradedInclusion F T hx hl]
  exact isEffective_gradedInclusion_ofRepresentation F T _ _ _

/-- Products of effective classes are effective. -/
theorem isEffective_mul {u v : GradedGrothendieckGroup.{uF, uV} F T}
    (hu : IsEffective F T u) (hv : IsEffective F T v) :
    letI := T.topology
    letI := gradedInductionRing F T hx hl
    IsEffective F T (u * v) := by
  let := T.topology
  let := gradedInductionRing F T hx hl
  intro m c
  have h1 : ∀ m' (c' : Label.{uF, uV} F T m'),
      0 ≤ ((coeff F T m c).comp ((gradedMultiplication F T hx).flip v)) (basisClass F T m' c') := by
    intro m' c'
    exact nonneg_of_isEffective F T
      (χ := (coeff F T m c).comp (gradedMultiplication F T hx (basisClass F T m' c')))
      (fun m'' c'' => isEffective_basisClass_mul F T hx hl m' m'' c' c'' m c) hv
  exact nonneg_of_isEffective F T h1 hu

end Products

/-! ### The adjusted operator on irreducible classes -/

private theorem effective_generator' {ι : Type*} (c : ι) :
    generator c ∈ effective := by
  classical
  intro d
  simp only [generator, Finsupp.single_apply]
  split_ifs <;> omega

/-- The support-adjusted operator sends every actual irreducible class to an actual
irreducible class, with sign `+1`. -/
theorem adjustedOperator_irreducible_eq (n : ℕ) :
    letI := T.topology
    ∀ (π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier))
      (hπ : π.IsIrreducible),
      ∃ (πD : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier))
        (hπD : πD.IsIrreducible),
        adjustedOperator.{uF, uV} F T n
            (GeneralLinear.finiteLengthClass n F.Carrier π (hasFiniteLength_of_isIrreducible hπ)) =
          GeneralLinear.finiteLengthClass n F.Carrier πD (hasFiniteLength_of_isIrreducible hπD) := by
  let := T.topology
  intro π hπ
  obtain ⟨πD, hπD, hD⟩ := irreducibleImage.{uF, uV} F T n π hπ
  let x := GeneralLinear.finiteLengthClass n F.Carrier π
    (hasFiniteLength_of_isIrreducible hπ)
  let y := GeneralLinear.finiteLengthClass n F.Carrier πD
    (hasFiniteLength_of_isIrreducible hπD)
  let c := SmoothRep.irreducibleIsoClass π hπ
  let d := SmoothRep.irreducibleIsoClass πD hπD
  obtain ⟨s, hs, hxy⟩ : ∃ s : ℤ, (s = 1 ∨ s = -1) ∧
      alternatingOperator.{uF, uV} F T n x = s • y := by
    rcases hD with hD | hD
    · exact ⟨1, Or.inl rfl, by simpa only [one_smul] using hD⟩
    · exact ⟨-1, Or.inr rfl, by simpa only [neg_one_smul] using hD⟩
  have hss : s * s = 1 := by
    rcases hs with rfl | rfl <;> norm_num
  have hyFactors : factorMap y = generator d :=
    (factorMap_ofRepresentation _ _).trans
      (compositionFactors_irreducible πD hπD (hasFiniteLength_of_isIrreducible hπD))
  have hc : supportSign.{uF, uV} F T n c = s := by
    apply supportSign_eq_of_effective F T n c s hs
    change s • factorMap (alternatingOperator F T n
      (SmoothRep.realizeIrreducibles ℂ (GeneralLinear n F.Carrier) (generator c))) ∈ effective
    rw [SmoothRep.realizeIrreducibles_generator_irreducibleIsoClass π hπ
      (hasFiniteLength_of_isIrreducible hπ)]
    change s • factorMap (alternatingOperator F T n x) ∈ effective
    rw [hxy, map_smul, smul_smul, hss, one_smul, hyFactors]
    exact effective_generator' d
  refine ⟨πD, hπD, ?_⟩
  rw [adjustedOperator_irreducible F T n π hπ, hc, hxy, smul_smul, hss, one_smul]

/-- The graded adjusted operator sends each basis class to a basis class of the same
rank. -/
theorem gradedAdjustedOperator_basisClass (m : ℕ) (c : Label.{uF, uV} F T m) :
    ∃ c' : Label.{uF, uV} F T m,
      gradedAdjustedOperator F T (basisClass F T m c) = basisClass F T m c' := by
  let := T.topology
  obtain ⟨π, hπ, rfl⟩ := IrreducibleIsoClass.exists_eq c
  obtain ⟨πD, hπD, h⟩ := adjustedOperator_irreducible_eq F T m π hπ
  refine ⟨GeneralLinear.irreducibleIsoClass m F.Carrier πD hπD, ?_⟩
  rw [basisClass_irreducibleIsoClass, basisClass_irreducibleIsoClass,
    gradedAdjustedOperator_homogeneous, h]

/-- The adjusted operator permutes basis classes, hence transports coefficients. -/
theorem coeff_gradedAdjustedOperator {m : ℕ} {c c' : Label.{uF, uV} F T m}
    (h : gradedAdjustedOperator F T (basisClass F T m c) = basisClass F T m c')
    (x : GradedGrothendieckGroup.{uF, uV} F T) :
    coeff F T m c' (gradedAdjustedOperator F T x) = coeff F T m c x := by
  let := T.topology
  refine apply_eq_of_basisClass F T
    (χ := (coeff F T m c').comp (gradedAdjustedOperator F T)) (φ := coeff F T m c) ?_
  intro m'' e _
  obtain ⟨e', he⟩ := gradedAdjustedOperator_basisClass F T m'' e
  change coeff F T m c' (gradedAdjustedOperator F T (basisClass F T m'' e)) = _
  rw [he]
  by_cases hm : m'' = m
  · subst hm
    by_cases hce : e = c
    · subst hce
      rw [he] at h
      rw [basisClass_injective F T h, coeff_basisClass_self, coeff_basisClass_self]
    · have hne : e' ≠ c' := by
        rintro rfl
        apply hce
        have h2 := congrArg (gradedAdjustedOperator F T) (he.trans h.symm)
        rw [adjustedInvolutivity F T (basisClass F T m'' e),
          adjustedInvolutivity F T (basisClass F T m'' c)] at h2
        exact basisClass_injective F T h2
      rw [coeff_basisClass_of_ne F T m'' hce, coeff_basisClass_of_ne F T m'' hne]
  · rw [basisClass, coeff_gradedInclusion_of_ne F T (Ne.symm hm), basisClass,
      coeff_gradedInclusion_of_ne F T (Ne.symm hm)]

/-! ### Classes of products of segment heads -/

theorem isIrreducible_of_isSegmentHead {Δ : T.Segment.{max uF uV, uF}}
    {π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier)}
    (hπ : T.IsSegmentHead Δ π) :
    letI := T.topology
    π.IsIrreducible := by
  obtain ⟨_, _, h⟩ := hπ
  exact h.1

/-- A product of irreducible blocks has finite length in every rank. -/
theorem hasFiniteLength_induced_of_irreducible {n : ℕ}
    (d : T.SegmentProductDatum.{max uF uV, uF} n)
    (hd : letI := T.topology; ∀ i, (d.blocks i).IsIrreducible) :
    letI := T.topology
    d.induced.HasFiniteLength := by
  let := T.topology
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact Derivative.ProductDerivativesFiniteLength.hasFiniteLength_of_iso
      (SegmentProductOrderedAssembly.zeroDatumUnitIso d).symm
      (binaryProductUnit_hasFiniteLength F T)
  · exact irreducibleProductFiniteLength.{uF, max uF uV} F T n hn d.shape d.blocks hd

/-- The class of a supplied segment head is the graded special class. -/
theorem gradedInclusion_eq_gradedSegmentSpecial (Δ : T.Segment.{max uF uV, uF})
    (π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier))
    (hπ : letI := T.topology; π.HasFiniteLength) (hs : T.IsSegmentHead Δ π) :
    letI := T.topology
    gradedInclusion F T Δ.degree (ofRepresentation π hπ) = gradedSegmentSpecial F T Δ := by
  let := T.topology
  unfold gradedSegmentSpecial
  rw [segmentSpecialClass_of_object F T Δ π hπ hs]
  rfl

section HeadProducts

variable (hx : BinaryProductExactnessStatement.{uF, uV} F T)
  (hl : GradedInductionRingLawsStatement F T hx)

/-- The class of a product of irreducible blocks whose classes are prescribed by a
function of their segments, for data with `k + 1` segments. -/
theorem gradedInclusion_induced_eq_prod_of_length_eq_succ
    (f : T.Segment.{max uF uV, uF} → GradedGrothendieckGroup.{uF, uV} F T) (k : ℕ) :
    letI := T.topology
    letI := gradedInductionRing F T hx hl
    ∀ {n : ℕ} (d : T.SegmentProductDatum.{max uF uV, uF} n), d.length = k + 1 →
      ∀ (hirr : ∀ i, (d.blocks i).IsIrreducible),
      (∀ i, gradedInclusion F T (d.segments i).degree
          (ofRepresentation (d.blocks i) (hasFiniteLength_of_isIrreducible (hirr i))) =
        f (d.segments i)) →
      ∀ hfin : d.induced.HasFiniteLength,
        gradedInclusion F T n (GeneralLinear.finiteLengthClass n F.Carrier d.induced hfin) =
          ∏ i, f (d.segments i) := by
  let := T.topology
  let := gradedInductionRing F T hx hl
  induction k with
  | zero =>
    intro n d h hirr hf hfin
    let i : Fin d.length := Fin.cast h.symm 0
    have hsz := d.shape.singleBlock_size h i
    have hb : (d.blocks i).HasFiniteLength := hasFiniteLength_of_isIrreducible (hirr i)
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
      _ = f (d.segments i) := hf i
      _ = ∏ j, f (d.segments j) :=
          (Fintype.prod_subsingleton (fun j => f (d.segments j)) i).symm
  | succ k ih =>
    intro n d h' hirr hf hfin
    have h : d.length = k + 2 := h'
    obtain ⟨e⟩ := SegmentProductSplit.nonempty_iso_binary d h
    let tl := SegmentProductSplit.tail d h
    have hab := d.shape.headRank_add_tailRank h
    have hA : (d.blocks (d.shape.headIndex h)).HasFiniteLength :=
      hasFiniteLength_of_isIrreducible (hirr _)
    have htl : ∀ j, (tl.blocks j).IsIrreducible := fun j => hirr _
    have hB : tl.induced.HasFiniteLength :=
      hasFiniteLength_induced_of_irreducible F T tl htl
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
      _ = f (d.segments (d.shape.headIndex h)) * ∏ j, f (tl.segments j) := by
          exact congrArg₂ (· * ·) (hf _) (ih tl rfl htl (fun j => hf _) hB)
      _ = ∏ i, f (d.segments i) :=
          (SegmentProductClass.prod_segments_eq_head_mul_tail F T _ d h).symm

/-- **The class of a product of segment heads.** -/
theorem gradedInclusion_induced_eq_prod_gradedSegmentSpecial {n : ℕ}
    (d : T.SegmentProductDatum.{max uF uV, uF} n) (hd : d.HasSegmentHeads)
    (hfin : letI := T.topology; d.induced.HasFiniteLength) :
    letI := T.topology
    letI := gradedInductionRing F T hx hl
    gradedInclusion F T n (GeneralLinear.finiteLengthClass n F.Carrier d.induced hfin) =
      ∏ i, gradedSegmentSpecial F T (d.segments i) := by
  let := T.topology
  let := gradedInductionRing F T hx hl
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
    exact gradedInclusion_induced_eq_prod_of_length_eq_succ F T hx hl _ k d hk
      (fun i => isIrreducible_of_isSegmentHead F T (hd i))
      (fun i => gradedInclusion_eq_gradedSegmentSpecial F T _ _ _ (hd i)) hfin

/-- The graded adjusted operator as a ring endomorphism. -/
def adjustedRingHom :
    letI := T.topology
    letI := gradedInductionRing F T hx hl
    GradedGrothendieckGroup.{uF, uV} F T →+* GradedGrothendieckGroup.{uF, uV} F T :=
  gradedOperatorRingHom F T (adjustedOperator F T) hx hl
    (gradedOperator_multiplicative_of_homogeneous F T (adjustedOperator F T) hx
      (adjustedHomogeneousMultiplicativity F T hx))
    (gradedAdjustedOperator_unit F T)

theorem adjustedRingHom_apply (x : GradedGrothendieckGroup.{uF, uV} F T) :
    adjustedRingHom F T hx hl x = gradedAdjustedOperator F T x := rfl

theorem gradedAdjustedOperator_mul (x y : GradedGrothendieckGroup.{uF, uV} F T) :
    letI := T.topology
    letI := gradedInductionRing F T hx hl
    gradedAdjustedOperator F T (x * y) =
      gradedAdjustedOperator F T x * gradedAdjustedOperator F T y := by
  let := T.topology
  let := gradedInductionRing F T hx hl
  exact map_mul (adjustedRingHom F T hx hl) x y

theorem gradedAdjustedOperator_gradedSegmentSpecial (Δ : T.Segment.{max uF uV, uF}) :
    gradedAdjustedOperator F T (gradedSegmentSpecial F T Δ) = gradedSegmentSocle F T Δ := by
  let := T.topology
  have h : gradedAdjustedOperator F T (gradedSegmentSocle F T Δ) = gradedSegmentSpecial F T Δ :=
    adjustedSegmentExchange F T Δ
  rw [← h]
  exact adjustedInvolutivity F T _

theorem zeta_multisegment_eq_prod {n : ℕ} (d : T.SegmentProductDatum.{max uF uV, uF} n) :
    letI := T.topology
    letI := gradedInductionRing F T hx hl
    zeta F T hx hl d.multisegment = ∏ i, gradedSegmentSocle F T (d.segments i) := by
  let := T.topology
  let := gradedInductionRing F T hx hl
  rw [← prod_map_zeta_singleton]
  simp only [zeta_singleton, SegmentProductDatum.multisegment, Multiset.map_coe,
    Multiset.prod_coe, List.map_ofFn, List.prod_ofFn, Function.comp_apply]

/-- The Aubert dual of the class of a product of segment heads is `ζ` of its
multisegment. -/
theorem gradedAdjustedOperator_headInduced {n : ℕ}
    (d : T.SegmentProductDatum.{max uF uV, uF} n) (hd : d.HasSegmentHeads)
    (hfin : letI := T.topology; d.induced.HasFiniteLength) :
    letI := T.topology
    gradedAdjustedOperator F T
        (gradedInclusion F T n (GeneralLinear.finiteLengthClass n F.Carrier d.induced hfin)) =
      zeta F T hx hl d.multisegment := by
  let := T.topology
  let := gradedInductionRing F T hx hl
  rw [gradedInclusion_induced_eq_prod_gradedSegmentSpecial F T hx hl d hd hfin,
    zeta_multisegment_eq_prod F T hx hl d, ← adjustedRingHom_apply F T hx hl, map_prod]
  exact Finset.prod_congr rfl fun i _ => gradedAdjustedOperator_gradedSegmentSpecial F T _

end HeadProducts

/-! ### Labels -/

section Labels

variable (hx : BinaryProductExactnessStatement.{uF, uV} F T)
  (hl : GradedInductionRingLawsStatement F T hx)
  (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)

include ψ in

/-- A label of `a` occurs in `ζ(a)` exactly once. -/
theorem coeff_zeta_eq_one_of_isLabel {a : T.Multisegment.{max uF uV, uF}} {m : ℕ}
    {c : Label.{uF, uV} F T m} (hc : IsLabel F T a m c) :
    coeff F T m c (zeta F T hx hl a) = 1 := by
  have h1 := one_le_coeff_zeta_of_isLabel F T hx hl hc
  have h2 := coeff_mul_le_weightedCount F T (w := labelWeight F T a) (labelWeight_nonneg F T a)
    (isEffective_zeta F T hx hl a) m c
  rw [labelWeight_of_isLabel F T hc, mul_one] at h2
  have h3 := labelCount_zeta_le_one F T hx hl ψ (highestDerivativeLabelStep F T ψ) a
  omega

include hx hl ψ in
/-- Labels of a multisegment are unique. -/
theorem isLabel_unique {a : T.Multisegment.{max uF uV, uF}} {m : ℕ}
    {c c' : Label.{uF, uV} F T m} (hc : IsLabel F T a m c) (hc' : IsLabel F T a m c') :
    c = c' := by
  by_contra hne
  have h1 := one_le_coeff_zeta_of_isLabel F T hx hl hc
  have h2 := one_le_coeff_zeta_of_isLabel F T hx hl hc'
  have heff := isEffective_sub_basisClass F T (isEffective_zeta F T hx hl a) h1
  have h3 := coeff_mul_le_weightedCount F T (w := labelWeight F T a) (labelWeight_nonneg F T a)
    heff m c'
  rw [map_sub, map_sub, coeff_basisClass_of_ne F T m hne, weightedCount_basisClass,
    labelWeight_of_isLabel F T hc, labelWeight_of_isLabel F T hc'] at h3
  have h4 := labelCount_zeta_le_one F T hx hl ψ (highestDerivativeLabelStep F T ψ) a
  omega

end Labels

/-- Every multisegment has a label in its degree. -/
theorem exists_isLabel_of_degree (a : T.Multisegment.{max uF uV, uF}) {m : ℕ}
    (hm : a.degree = m) : ∃ c : Label.{uF, uV} F T m, IsLabel F T a m c := by
  let := T.topology
  subst hm
  obtain ⟨d, hda, ho, hs⟩ :=
    (Classification.multisegmentConstituentDataExistence.{uF, uV} F T a).1
  obtain ⟨π, hπ⟩ :=
    Classification.orderedMultisegmentSocleExistence.{uF, uV} F T a.degree d ho hs
  have hz := hπ.isZelevinskySubrepresentation
  exact ⟨GeneralLinear.irreducibleIsoClass a.degree F.Carrier π hz.2.2.1, π, hz.2.2.1, rfl,
    d, hda, hz⟩

/-- Langlands heads are irreducible. -/
theorem isIrreducible_of_isLanglandsHead {m : ℕ} {a : T.Multisegment.{max uF uV, uF}}
    {π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear m F.Carrier)}
    (h : a.IsLanglandsHead π) :
    letI := T.topology
    π.IsIrreducible := by
  obtain ⟨_, _, _, _, hhead⟩ := h
  exact hhead.1

/-- The degree of a multisegment with a Langlands head in rank `m` is `m`. -/
theorem degree_of_isLanglandsHead {m : ℕ} {a : T.Multisegment.{max uF uV, uF}}
    {π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear m F.Carrier)}
    (h : a.IsLanglandsHead π) : a.degree = m := by
  obtain ⟨d, rfl, -⟩ := h
  exact degree_multisegment F T d

/-! ### Langlands heads as duals of labels -/

section Duality

variable (hx : BinaryProductExactnessStatement.{uF, uV} F T)
  (hl : GradedInductionRingLawsStatement F T hx)
  (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)

/-- The Aubert dual of a Langlands head of `a` occurs in `ζ(a)`. -/
theorem coeff_zeta_pos_of_isLanglandsHead {m : ℕ} {a : T.Multisegment.{max uF uV, uF}}
    {π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear m F.Carrier)}
    (hπ : letI := T.topology; π.IsIrreducible) (ha : a.IsLanglandsHead π)
    {c' : Label.{uF, uV} F T m}
    (hc' : letI := T.topology
      gradedAdjustedOperator F T
        (basisClass F T m (GeneralLinear.irreducibleIsoClass m F.Carrier π hπ)) =
      basisClass F T m c') :
    0 < coeff F T m c' (zeta F T hx hl a) := by
  let := T.topology
  obtain ⟨d, hda, -, hh, hhead⟩ := ha
  have hfin : d.induced.HasFiniteLength :=
    hasFiniteLength_induced_of_irreducible F T d fun i => isIrreducible_of_isSegmentHead F T (hh i)
  obtain ⟨-, q, hq, -⟩ := hhead
  have hsub : SmoothRep.IsSubquotient π d.induced :=
    SmoothRep.IsQuotient.isSubquotient ⟨SmoothRep.ofHom q, hq⟩
  have hmult : 0 < coeff F T m (GeneralLinear.irreducibleIsoClass m F.Carrier π hπ)
      (gradedInclusion F T m (GeneralLinear.finiteLengthClass m F.Carrier d.induced hfin)) := by
    rw [coeff_gradedInclusion_ofRepresentation F T m _ hfin π hπ]
    exact_mod_cast (compositionMultiplicity_pos_iff_isSubquotient ⟨_, hfin⟩ π hπ).mpr hsub
  rw [← coeff_gradedAdjustedOperator F T hc', gradedAdjustedOperator_headInduced F T hx hl d hh hfin,
    hda] at hmult
  exact hmult

include hx hl ψ in
/-- **Langlands heads are the Aubert duals of Zelevinsky labels.** The adjusted Aubert
operator sends the label of `a` to the class of every Langlands head of `a`. -/
theorem gradedAdjustedOperator_label (a : T.Multisegment.{max uF uV, uF}) :
    letI := T.topology
    ∀ (m : ℕ) (c : Label.{uF, uV} F T m), IsLabel F T a m c →
      ∀ (π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear m F.Carrier))
        (hπ : π.IsIrreducible), a.IsLanglandsHead π →
        gradedAdjustedOperator F T (basisClass F T m c) =
          basisClass F T m (GeneralLinear.irreducibleIsoClass m F.Carrier π hπ) := by
  let := T.topology
  induction a using (Multisegment.wellFounded_rankLT (T := T)).induction with
  | _ a ih =>
  intro m c hc π hπ ha
  obtain ⟨c', hc'⟩ := gradedAdjustedOperator_basisClass F T m
    (GeneralLinear.irreducibleIsoClass m F.Carrier π hπ)
  have hinv : gradedAdjustedOperator F T (basisClass F T m c') =
      basisClass F T m (GeneralLinear.irreducibleIsoClass m F.Carrier π hπ) := by
    rw [← hc', adjustedInvolutivity]
  have hpos := coeff_zeta_pos_of_isLanglandsHead F T hx hl hπ ha hc'
  obtain ⟨b, hb⟩ := exists_isLabel F T (Classification.multisegmentSocleExhaustion F T) m c'
  have hba := rankLE_of_coeff_zeta_pos F T hx hl ψ (highestDerivativeLabelStep F T ψ) m c' b a
    hb hpos
  by_cases hne : b = a
  · subst hne
    rw [isLabel_unique F T hx hl ψ hc hb, hinv]
  · exfalso
    have hdeg : b.degree = m := IsLabel.degree F T hb
    subst hdeg
    obtain ⟨πb, hπb⟩ := Classification.multisegmentHeadExistence F T b
    have hπbirr := isIrreducible_of_isLanglandsHead F T hπb
    have h1 := ih b ⟨hba, hne⟩ b.degree c' hb πb hπbirr hπb
    rw [h1] at hinv
    have hiso : Nonempty (π ≅ πb) :=
      (SmoothRep.irreducibleIsoClass_eq_iff hπ hπbirr).mp (basisClass_injective F T hinv).symm
    exact hne ((Classification.multisegmentHeadClassification F T b.degree a b π πb ha hπb).mpr
      hiso).symm

end Duality

/-! ### Zelevinsky's Proposition 8.4 for labels -/

section Product

variable (hx : BinaryProductExactnessStatement.{uF, uV} F T)
  (hl : GradedInductionRingLawsStatement F T hx)
  (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)

/-- A positive coefficient of `x * y`, with `y` effective, comes from a basis class
occurring in `y`. -/
theorem exists_coeff_pos_mul_right (x : GradedGrothendieckGroup.{uF, uV} F T)
    {y : GradedGrothendieckGroup.{uF, uV} F T} (hy : IsEffective F T y) {k : ℕ}
    {e : Label.{uF, uV} F T k}
    (h : letI := T.topology
      letI := gradedInductionRing F T hx hl
      0 < coeff F T k e (x * y)) :
    letI := T.topology
    letI := gradedInductionRing F T hx hl
    ∃ (n : ℕ) (Y : Label.{uF, uV} F T n), 0 < coeff F T n Y y ∧
      0 < coeff F T k e (x * basisClass F T n Y) := by
  let := T.topology
  let := gradedInductionRing F T hx hl
  exact exists_coeff_pos_of_pos F T (χ := (coeff F T k e).comp (gradedMultiplication F T hx x))
    hy h

/-- A positive coefficient of `x * y`, with `x` effective, comes from a basis class
occurring in `x`. -/
theorem exists_coeff_pos_mul_left {x : GradedGrothendieckGroup.{uF, uV} F T}
    (hx' : IsEffective F T x) (y : GradedGrothendieckGroup.{uF, uV} F T) {k : ℕ}
    {e : Label.{uF, uV} F T k}
    (h : letI := T.topology
      letI := gradedInductionRing F T hx hl
      0 < coeff F T k e (x * y)) :
    letI := T.topology
    letI := gradedInductionRing F T hx hl
    ∃ (m : ℕ) (X : Label.{uF, uV} F T m), 0 < coeff F T m X x ∧
      0 < coeff F T k e (basisClass F T m X * y) := by
  let := T.topology
  let := gradedInductionRing F T hx hl
  exact exists_coeff_pos_of_pos F T
    (χ := (coeff F T k e).comp ((gradedMultiplication F T hx).flip y)) hx' h

/-- If `X` occurs in `u` and `Y` occurs in `v`, both effective, then `u v - X Y` is
effective. -/
theorem isEffective_mul_sub_basisClass_mul {u v : GradedGrothendieckGroup.{uF, uV} F T}
    (hu : IsEffective F T u) (hv : IsEffective F T v) {m n : ℕ} {X : Label.{uF, uV} F T m}
    {Y : Label.{uF, uV} F T n} (hX : 1 ≤ coeff F T m X u) (hY : 1 ≤ coeff F T n Y v) :
    letI := T.topology
    letI := gradedInductionRing F T hx hl
    IsEffective F T (u * v - basisClass F T m X * basisClass F T n Y) := by
  let := T.topology
  let := gradedInductionRing F T hx hl
  have e : u * v - basisClass F T m X * basisClass F T n Y =
      basisClass F T m X * (v - basisClass F T n Y) + (u - basisClass F T m X) * v := by
    ring
  rw [e]
  exact IsEffective.add F T
    (isEffective_mul F T hx hl (isEffective_basisClass F T m X)
      (isEffective_sub_basisClass F T hv hY))
    (isEffective_mul F T hx hl (isEffective_sub_basisClass F T hu hX) hv)

include ψ in
/-- If a label of `a + b` occurs in `X Y`, where `X` occurs in `ζ(a)` and `Y` occurs in
`ζ(b)`, then `X` is the label of `a` and `Y` is the label of `b`. -/
theorem isLabel_of_coeff_basisClass_mul_pos {a b : T.Multisegment.{max uF uV, uF}} {k : ℕ}
    {e : Label.{uF, uV} F T k} (he : IsLabel F T (a + b) k e) {m n : ℕ}
    {X : Label.{uF, uV} F T m} {Y : Label.{uF, uV} F T n}
    (hX : 0 < coeff F T m X (zeta F T hx hl a)) (hY : 0 < coeff F T n Y (zeta F T hx hl b))
    (hXY : letI := T.topology
      letI := gradedInductionRing F T hx hl
      0 < coeff F T k e (basisClass F T m X * basisClass F T n Y)) :
    IsLabel F T a m X ∧ IsLabel F T b n Y := by
  let := T.topology
  let := gradedInductionRing F T hx hl
  have hstep := highestDerivativeLabelStep F T ψ
  have hex := Classification.multisegmentSocleExhaustion F T
  obtain ⟨a', ha'⟩ := exists_isLabel F T hex m X
  obtain ⟨b', hb'⟩ := exists_isLabel F T hex n Y
  have hra := rankLE_of_coeff_zeta_pos F T hx hl ψ hstep m X a' a ha' hX
  have hrb := rankLE_of_coeff_zeta_pos F T hx hl ψ hstep n Y b' b hb' hY
  have heff := isEffective_mul_sub_basisClass_mul F T hx hl (isEffective_zeta F T hx hl a')
    (isEffective_zeta F T hx hl b') (one_le_coeff_zeta_of_isLabel F T hx hl ha')
    (one_le_coeff_zeta_of_isLabel F T hx hl hb') k e
  have hpos : 0 < coeff F T k e (zeta F T hx hl (a' + b')) := by
    rw [map_sub] at heff
    rw [zeta_add]
    omega
  have hr := rankLE_of_coeff_zeta_pos F T hx hl ψ hstep k e (a + b) (a' + b') he hpos
  have hcount : ∀ I, Multisegment.containmentCount I a' = Multisegment.containmentCount I a ∧
      Multisegment.containmentCount I b' = Multisegment.containmentCount I b := by
    intro I
    have h1 := hr.2 I
    rw [Multisegment.containmentCount_add, Multisegment.containmentCount_add] at h1
    have h2 := hra.2 I
    have h3 := hrb.2 I
    omega
  have ha : a' = a := Multisegment.eq_of_containmentCount_eq fun I => (hcount I).1
  have hb : b' = b := Multisegment.eq_of_containmentCount_eq fun I => (hcount I).2
  exact ⟨ha ▸ ha', hb ▸ hb'⟩

include ψ in
/-- **Zelevinsky 1980, Proposition 8.4, for labels.** The label of `a + b` occurs in the
product of the labels of `a` and `b`. -/
theorem one_le_coeff_label_mul {a b : T.Multisegment.{max uF uV, uF}} {m n : ℕ}
    {ca : Label.{uF, uV} F T m} {cb : Label.{uF, uV} F T n}
    {cab : Label.{uF, uV} F T (m + n)} (ha : IsLabel F T a m ca) (hb : IsLabel F T b n cb)
    (hab : IsLabel F T (a + b) (m + n) cab) :
    letI := T.topology
    letI := gradedInductionRing F T hx hl
    1 ≤ coeff F T (m + n) cab (basisClass F T m ca * basisClass F T n cb) := by
  let := T.topology
  let := gradedInductionRing F T hx hl
  have h1 := coeff_zeta_eq_one_of_isLabel F T hx hl ψ ha
  have h2 := coeff_zeta_eq_one_of_isLabel F T hx hl ψ hb
  have hR := isEffective_sub_basisClass F T (isEffective_zeta F T hx hl a) h1.ge
  have hS := isEffective_sub_basisClass F T (isEffective_zeta F T hx hl b) h2.ge
  have hR0 : coeff F T m ca (zeta F T hx hl a - basisClass F T m ca) = 0 := by
    rw [map_sub, h1, coeff_basisClass_self, sub_self]
  have hS0 : coeff F T n cb (zeta F T hx hl b - basisClass F T n cb) = 0 := by
    rw [map_sub, h2, coeff_basisClass_self, sub_self]
  have hdecomp : zeta F T hx hl (a + b) = basisClass F T m ca * basisClass F T n cb +
      (basisClass F T m ca * (zeta F T hx hl b - basisClass F T n cb) +
        (zeta F T hx hl a - basisClass F T m ca) * zeta F T hx hl b) := by
    rw [zeta_add]
    ring
  have hcS : coeff F T (m + n) cab
      (basisClass F T m ca * (zeta F T hx hl b - basisClass F T n cb)) ≤ 0 := by
    by_contra hpos
    obtain ⟨n', Y, hY, hcY⟩ := exists_coeff_pos_mul_right F T hx hl _ hS (not_le.mp hpos)
    have hYb : 0 < coeff F T n' Y (zeta F T hx hl b) := by
      have := isEffective_basisClass F T n cb n' Y
      rw [map_sub] at hY
      omega
    have hca : 0 < coeff F T m ca (zeta F T hx hl a) := by omega
    obtain ⟨-, hYl⟩ := isLabel_of_coeff_basisClass_mul_pos F T hx hl ψ hab hca hYb hcY
    have hdeg : n' = n := (IsLabel.degree F T hYl).symm.trans (IsLabel.degree F T hb)
    subst hdeg
    rw [isLabel_unique F T hx hl ψ hYl hb, hS0] at hY
    exact lt_irrefl 0 hY
  have hcR : coeff F T (m + n) cab
      ((zeta F T hx hl a - basisClass F T m ca) * zeta F T hx hl b) ≤ 0 := by
    by_contra hpos
    obtain ⟨m', X, hX, hcX⟩ := exists_coeff_pos_mul_left F T hx hl hR _ (not_le.mp hpos)
    obtain ⟨n', Y, hY, hcY⟩ :=
      exists_coeff_pos_mul_right F T hx hl _ (isEffective_zeta F T hx hl b) hcX
    have hXa : 0 < coeff F T m' X (zeta F T hx hl a) := by
      have := isEffective_basisClass F T m ca m' X
      rw [map_sub] at hX
      omega
    obtain ⟨hXl, -⟩ := isLabel_of_coeff_basisClass_mul_pos F T hx hl ψ hab hXa hY hcY
    have hdeg : m' = m := (IsLabel.degree F T hXl).symm.trans (IsLabel.degree F T ha)
    subst hdeg
    rw [isLabel_unique F T hx hl ψ hXl ha, hR0] at hX
    exact lt_irrefl 0 hX
  have h3 := one_le_coeff_zeta_of_isLabel F T hx hl hab
  rw [hdecomp, map_add, map_add] at h3
  omega

end Product

end LanglandsHeadDuality

end Langlands.Aubert
