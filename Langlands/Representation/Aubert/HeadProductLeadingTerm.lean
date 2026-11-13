import Langlands.Representation.Aubert.LanglandsHeadDuality
import Langlands.Representation.Aubert.UniformLengthRankOrder
import Langlands.Representation.Classification.OrderedMultisegmentHeadClassificationProof

/-! # Rank bounds and leading multiplicity for products of actual Langlands heads -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.Aubert.HeadProductLeadingTerm

open PadicField.TopologicalData SmoothRep
open SmoothRep.IrreducibleGrothendieckProof SegmentPolynomialSurjectivity

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- Every multisegment of degree `m` has a Langlands head in rank `m`. -/
theorem exists_head {a : T.Multisegment.{max uF uV, uF}} {m : ℕ} (hm : a.degree = m) :
    letI := T.topology
    ∃ (d : T.SegmentProductDatum.{max uF uV, uF} m)
      (L : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear m F.Carrier)),
      d.multisegment = a ∧ d.IsLanglandsHead L := by
  let := T.topology
  subst m
  obtain ⟨L, d, hd, hL⟩ := Classification.multisegmentHeadExistence.{uF, uV} F T a
  exact ⟨d, L, hd, hL⟩

/-- Every supplied weak Langlands head has a socle label with the same
multisegment, whose adjusted class is that actual head class. -/
theorem exists_socleLabel_of_isLanglandsQuotient {n : ℕ}
    (d : T.SegmentProductDatum.{max uF uV, uF} n) :
    letI := T.topology
    ∀ (L : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier))
      (hL : d.IsLanglandsQuotient L),
      ∃ c : Label.{uF, uV} F T n, IsLabel F T d.multisegment n c ∧
        gradedAdjustedOperator F T (basisClass F T n c) =
          basisClass F T n (GeneralLinear.irreducibleIsoClass n F.Carrier L hL.2.2.1) := by
  let := T.topology
  intro L hL
  obtain ⟨ψ⟩ := HarmonicAnalysis.padicUnitaryAdditiveCharacterExists F T
  let hx := binaryProductExactness.{uF, uV} F T
  let hl := gradedInductionRingLaws F T hx
  have hdeg : d.multisegment.degree = n := degree_multisegment F T d
  obtain ⟨c, hc⟩ := LanglandsHeadDuality.exists_isLabel_of_degree F T d.multisegment hdeg
  obtain ⟨da, La, hda, hLa⟩ := exists_head F T hdeg
  have hLairr : La.IsIrreducible := hLa.2.2.1
  have hex := LanglandsHeadDuality.gradedAdjustedOperator_label F T hx hl ψ d.multisegment n c hc
    La hLairr ⟨da, hda, hLa⟩
  have hiso : Nonempty (La ≅ L) :=
    (Classification.orderedMultisegmentHeadClassification.{uF, uV} F T n da d La L
      hLa.isLanglandsQuotient hL).mp hda
  have hclass : GeneralLinear.irreducibleIsoClass n F.Carrier La hLairr =
      GeneralLinear.irreducibleIsoClass n F.Carrier L hL.2.2.1 :=
    (SmoothRep.irreducibleIsoClass_eq_iff _ _).mpr hiso
  exact ⟨c, hc, hex.trans (congrArg (basisClass F T n) hclass)⟩

/-- The coefficient of a label in the product of two labels is the actual
composition multiplicity in the product of their adjusted images. -/
theorem coeff_mul_eq_compositionMultiplicity
    (hx : BinaryProductExactnessStatement.{uF, uV} F T) {m n : ℕ}
    (cA : Label.{uF, uV} F T m) (cB : Label.{uF, uV} F T n)
    (cC : Label.{uF, uV} F T (m + n)) :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear m F.Carrier))
      (B : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier))
      (C : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (m + n) F.Carrier))
      (hA : A.IsIrreducible) (hB : B.IsIrreducible) (hC : C.IsIrreducible),
      gradedAdjustedOperator F T (basisClass F T m cA) =
        basisClass F T m (GeneralLinear.irreducibleIsoClass m F.Carrier A hA) →
      gradedAdjustedOperator F T (basisClass F T n cB) =
        basisClass F T n (GeneralLinear.irreducibleIsoClass n F.Carrier B hB) →
      gradedAdjustedOperator F T (basisClass F T (m + n) cC) =
        basisClass F T (m + n) (GeneralLinear.irreducibleIsoClass (m + n) F.Carrier C hC) →
      ∀ hfin : ((T.binaryNormalizedProductFunctor.{uF, max uF uV} m n).obj (A, B)).HasFiniteLength,
      coeff F T (m + n) cC
        (gradedMultiplication F T hx (basisClass F T m cA) (basisClass F T n cB)) =
        (compositionMultiplicity
          ⟨(T.binaryNormalizedProductFunctor.{uF, max uF uV} m n).obj (A, B), hfin⟩ C : ℤ) := by
  let := T.topology
  intro A B C hA hB hC hDA hDB hDC hfin
  rw [← LanglandsHeadDuality.coeff_gradedAdjustedOperator F T hDC]
  have hm := gradedOperator_multiplicative_of_homogeneous F T (adjustedOperator F T) hx
    (adjustedHomogeneousMultiplicativity F T hx)
  have hm' := hm (basisClass F T m cA) (basisClass F T n cB)
  change gradedAdjustedOperator F T _ = gradedMultiplication F T hx
    (gradedAdjustedOperator F T _) (gradedAdjustedOperator F T _) at hm'
  rw [hm', hDA, hDB, basisClass_irreducibleIsoClass, basisClass_irreducibleIsoClass,
    gradedMultiplication_homogeneous]
  change coeff F T (m + n) _ (gradedInclusion F T (m + n) (binaryProductK0 F T hx m n
    (FiniteLengthGrothendieckGroup.ofObject ⟨A, hasFiniteLength_of_isIrreducible hA⟩)
    (FiniteLengthGrothendieckGroup.ofObject ⟨B, hasFiniteLength_of_isIrreducible hB⟩))) = _
  rw [binaryProductK0_classes]
  change coeff F T (m + n) (GeneralLinear.irreducibleIsoClass (m + n) F.Carrier C hC)
    (gradedInclusion F T (m + n) (GeneralLinear.finiteLengthClass (m + n) F.Carrier
      ((T.binaryNormalizedProductFunctor.{uF, max uF uV} m n).obj (A, B)) hfin)) = _
  exact coeff_gradedInclusion_ofRepresentation F T (m + n) _ hfin C hC

section Labels

variable (hx : BinaryProductExactnessStatement.{uF, uV} F T)
  (hl : GradedInductionRingLawsStatement F T hx)
  (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)

include hl ψ in
/-- A label occurring in the product of the labels of `a` and `b` is the label
of a multisegment rank-lower than `a + b`. -/
theorem rankLE_of_coeff_label_mul_pos {a b q : T.Multisegment.{max uF uV, uF}} {m n k : ℕ}
    {c : Label.{uF, uV} F T m} {d : Label.{uF, uV} F T n} {e : Label.{uF, uV} F T k}
    (hc : IsLabel F T a m c) (hd : IsLabel F T b n d) (he : IsLabel F T q k e)
    (hpos : 0 < coeff F T k e
      (gradedMultiplication F T hx (basisClass F T m c) (basisClass F T n d))) :
    Multisegment.RankLE q (a + b) := by
  let := T.topology
  let := gradedInductionRing F T hx hl
  have heff := LanglandsHeadDuality.isEffective_mul_sub_basisClass_mul F T hx hl
    (isEffective_zeta F T hx hl a) (isEffective_zeta F T hx hl b)
    (one_le_coeff_zeta_of_isLabel F T hx hl hc) (one_le_coeff_zeta_of_isLabel F T hx hl hd) k e
  change 0 < coeff F T k e (basisClass F T m c * basisClass F T n d) at hpos
  have hz : 0 < coeff F T k e (zeta F T hx hl (a + b)) := by
    rw [map_sub] at heff
    rw [zeta_add]
    omega
  exact rankLE_of_coeff_zeta_pos F T hx hl ψ (highestDerivativeLabelStep F T ψ) k e q (a + b)
    he hz

include hl ψ in
/-- The label of `a + b` occurs exactly once in the product of the labels of
`a` and `b`. -/
theorem coeff_label_mul_eq_one {a b : T.Multisegment.{max uF uV, uF}} {m n : ℕ}
    {c : Label.{uF, uV} F T m} {d : Label.{uF, uV} F T n} {e : Label.{uF, uV} F T (m + n)}
    (hc : IsLabel F T a m c) (hd : IsLabel F T b n d) (he : IsLabel F T (a + b) (m + n) e) :
    coeff F T (m + n) e
      (gradedMultiplication F T hx (basisClass F T m c) (basisClass F T n d)) = 1 := by
  let := T.topology
  let := gradedInductionRing F T hx hl
  have h1 := LanglandsHeadDuality.one_le_coeff_label_mul F T hx hl ψ hc hd he
  have heff := LanglandsHeadDuality.isEffective_mul_sub_basisClass_mul F T hx hl
    (isEffective_zeta F T hx hl a) (isEffective_zeta F T hx hl b)
    (one_le_coeff_zeta_of_isLabel F T hx hl hc) (one_le_coeff_zeta_of_isLabel F T hx hl hd)
    (m + n) e
  have hz := LanglandsHeadDuality.coeff_zeta_eq_one_of_isLabel F T hx hl ψ he
  rw [map_sub] at heff
  rw [zeta_add] at hz
  change coeff F T (m + n) e (basisClass F T m c * basisClass F T n d) = 1
  omega

end Labels

/-- Every actual Langlands-head constituent of a product of two supplied
Langlands heads is rank-lower than the sum of their multisegments. -/
theorem rankLE_of_isSubquotient {m n : ℕ}
    (dA : T.SegmentProductDatum.{max uF uV, uF} m)
    (dB : T.SegmentProductDatum.{max uF uV, uF} n)
    (dC : T.SegmentProductDatum.{max uF uV, uF} (m + n)) :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear m F.Carrier))
      (B : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier))
      (C : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (m + n) F.Carrier)),
      dA.IsLanglandsQuotient A → dB.IsLanglandsQuotient B → dC.IsLanglandsQuotient C →
      IsSubquotient C ((T.binaryNormalizedProductFunctor.{uF, max uF uV} m n).obj (A, B)) →
      Multisegment.RankLE dC.multisegment (dA.multisegment + dB.multisegment) := by
  let := T.topology
  intro A B C hA hB hC hsub
  obtain ⟨ψ⟩ := HarmonicAnalysis.padicUnitaryAdditiveCharacterExists F T
  let hx := binaryProductExactness.{uF, uV} F T
  let hl := gradedInductionRingLaws F T hx
  obtain ⟨cA, hcA, hDA⟩ := exists_socleLabel_of_isLanglandsQuotient F T dA A hA
  obtain ⟨cB, hcB, hDB⟩ := exists_socleLabel_of_isLanglandsQuotient F T dB B hB
  obtain ⟨cC, hcC, hDC⟩ := exists_socleLabel_of_isLanglandsQuotient F T dC C hC
  have hfin := binaryProduct_preservesFiniteLength F T m n A B
    (hasFiniteLength_of_isIrreducible hA.2.2.1) (hasFiniteLength_of_isIrreducible hB.2.2.1)
  have hpos : 0 < coeff F T (m + n) cC
      (gradedMultiplication F T hx (basisClass F T m cA) (basisClass F T n cB)) := by
    rw [coeff_mul_eq_compositionMultiplicity F T hx cA cB cC A B C
      hA.2.2.1 hB.2.2.1 hC.2.2.1 hDA hDB hDC hfin]
    exact_mod_cast (compositionMultiplicity_pos_iff_isSubquotient
      ⟨_, hfin⟩ C hC.2.2.1).mpr hsub
  exact rankLE_of_coeff_label_mul_pos F T hx hl ψ hcA hcB hcC hpos

/-- The actual head labelled by the sum occurs exactly once in the product
of the two supplied Langlands heads. -/
theorem compositionMultiplicity_eq_one {m n : ℕ}
    (dA : T.SegmentProductDatum.{max uF uV, uF} m)
    (dB : T.SegmentProductDatum.{max uF uV, uF} n)
    (dC : T.SegmentProductDatum.{max uF uV, uF} (m + n))
    (hmult : dC.multisegment = dA.multisegment + dB.multisegment) :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear m F.Carrier))
      (B : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier))
      (C : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (m + n) F.Carrier)),
      dA.IsLanglandsQuotient A → dB.IsLanglandsQuotient B → dC.IsLanglandsQuotient C →
      ∀ hfin : ((T.binaryNormalizedProductFunctor.{uF, max uF uV} m n).obj (A, B)).HasFiniteLength,
        compositionMultiplicity
          ⟨(T.binaryNormalizedProductFunctor.{uF, max uF uV} m n).obj (A, B), hfin⟩ C = 1 := by
  let := T.topology
  intro A B C hA hB hC hfin
  obtain ⟨ψ⟩ := HarmonicAnalysis.padicUnitaryAdditiveCharacterExists F T
  let hx := binaryProductExactness.{uF, uV} F T
  let hl := gradedInductionRingLaws F T hx
  obtain ⟨cA, hcA, hDA⟩ := exists_socleLabel_of_isLanglandsQuotient F T dA A hA
  obtain ⟨cB, hcB, hDB⟩ := exists_socleLabel_of_isLanglandsQuotient F T dB B hB
  obtain ⟨cC, hcC, hDC⟩ := exists_socleLabel_of_isLanglandsQuotient F T dC C hC
  have hcC' : IsLabel F T (dA.multisegment + dB.multisegment) (m + n) cC := hmult ▸ hcC
  have he := coeff_label_mul_eq_one F T hx hl ψ hcA hcB hcC'
  rw [coeff_mul_eq_compositionMultiplicity F T hx cA cB cC A B C
    hA.2.2.1 hB.2.2.1 hC.2.2.1 hDA hDB hDC hfin] at he
  exact_mod_cast he

/-- A constituent head below a uniform-length sum, with a different
multisegment, contains a longer segment. -/
theorem exists_longer_segment_of_isSubquotient {m n : ℕ}
    (dA : T.SegmentProductDatum.{max uF uV, uF} m)
    (dB : T.SegmentProductDatum.{max uF uV, uF} n)
    (dC : T.SegmentProductDatum.{max uF uV, uF} (m + n)) :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear m F.Carrier))
      (B : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier))
      (C : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (m + n) F.Carrier)),
      dA.IsLanglandsQuotient A → dB.IsLanglandsQuotient B → dC.IsLanglandsQuotient C →
      ∀ {l : ℕ},
      IsSubquotient C ((T.binaryNormalizedProductFunctor.{uF, max uF uV} m n).obj (A, B)) →
      (∀ Δ ∈ dA.multisegment + dB.multisegment, Δ.length = l) →
      dC.multisegment ≠ dA.multisegment + dB.multisegment →
      ∃ Δ ∈ dC.multisegment, l < Δ.length := by
  intro A B C hA hB hC l hsub hlen hne
  exact (rankLE_of_isSubquotient F T dA dB dC A B C hA hB hC hsub).exists_longer_segment hlen hne

end Langlands.Aubert.HeadProductLeadingTerm
