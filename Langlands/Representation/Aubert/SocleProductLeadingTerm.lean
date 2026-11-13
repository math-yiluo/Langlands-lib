import Langlands.Representation.Aubert.RankOrderProducts
import Langlands.Representation.Aubert.SegmentPolynomialSurjectivity
import Langlands.Representation.Aubert.BinaryProductExactnessProof
import Langlands.Representation.Aubert.GradedInductionRingLawsProof
import Langlands.Representation.Classification.MultisegmentSocleExhaustionProof
import Langlands.Representation.Aubert.SocleProductLeadingTermStatement

/-! # Rank triangularity and leading coefficients of products of socle labels -/

noncomputable section

namespace Langlands.Aubert.SocleProductLeadingTerm

open PadicField.TopologicalData SmoothRep
open SmoothRep.IrreducibleGrothendieckProof SegmentPolynomialSurjectivity

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)
    (hx : BinaryProductExactnessStatement.{uF, uV} F T)
    (hl : GradedInductionRingLawsStatement F T hx)

/-- Induction of two irreducible basis classes is effective. -/
theorem isEffective_mul_basisClass (m n : ℕ)
    (c : Label.{uF, uV} F T m) (d : Label.{uF, uV} F T n) :
    letI := T.topology
    letI := gradedInductionRing F T hx hl
    IsEffective F T (basisClass F T m c * basisClass F T n d) := by
  let := T.topology
  let := gradedInductionRing F T hx hl
  obtain ⟨A, hA, rfl⟩ := IrreducibleIsoClass.exists_eq c
  obtain ⟨B, hB, rfl⟩ := IrreducibleIsoClass.exists_eq d
  rw [basisClass_irreducibleIsoClass, basisClass_irreducibleIsoClass]
  change IsEffective F T (gradedMultiplication F T hx
    (gradedInclusion F T m (GeneralLinear.finiteLengthClass m F.Carrier A
      (hasFiniteLength_of_isIrreducible hA)))
    (gradedInclusion F T n (GeneralLinear.finiteLengthClass n F.Carrier B
      (hasFiniteLength_of_isIrreducible hB))))
  rw [gradedMultiplication_homogeneous]
  change IsEffective F T (gradedInclusion F T (m + n) (binaryProductK0 F T hx m n
    (FiniteLengthGrothendieckGroup.ofObject ⟨A, hasFiniteLength_of_isIrreducible hA⟩)
    (FiniteLengthGrothendieckGroup.ofObject ⟨B, hasFiniteLength_of_isIrreducible hB⟩)))
  rw [binaryProductK0_classes]
  exact isEffective_gradedInclusion_ofRepresentation F T _ _ _

/-- The product of any two effective classes is effective. -/
theorem isEffective_mul {x y : GradedGrothendieckGroup.{uF, uV} F T}
    (hxx : IsEffective F T x) (hyy : IsEffective F T y) :
    letI := T.topology
    letI := gradedInductionRing F T hx hl
    IsEffective F T (x * y) := by
  let := T.topology
  let := gradedInductionRing F T hx hl
  intro m c
  apply nonneg_of_isEffective F T
    (χ := (coeff F T m c).comp ((gradedMultiplication F T hx).flip y)) ?_ hxx
  intro n d
  exact nonneg_of_isEffective F T
    (χ := (coeff F T m c).comp (gradedMultiplication F T hx (basisClass F T n d)))
    (fun k e => isEffective_mul_basisClass F T hx hl n k d e m c) hyy

/-- Effective differences can be multiplied on the right. -/
theorem coeff_mul_le_mul_right
    {x x' y : GradedGrothendieckGroup.{uF, uV} F T}
    (h : IsEffective F T (x' - x)) (hy : IsEffective F T y)
    (m : ℕ) (c : Label.{uF, uV} F T m) :
    letI := T.topology
    letI := gradedInductionRing F T hx hl
    coeff F T m c (x * y) ≤ coeff F T m c (x' * y) := by
  let := T.topology
  let := gradedInductionRing F T hx hl
  have hh := isEffective_mul F T hx hl h hy m c
  simpa only [sub_mul, map_sub, sub_nonneg] using hh

/-- The coefficients of a product of two socle labels are bounded by those
of the product of all corresponding segment socles. -/
theorem coeff_mul_le_zeta
    {a b : T.Multisegment.{max uF uV, uF}} {m n : ℕ}
    {c : Label.{uF, uV} F T m} {d : Label.{uF, uV} F T n}
    (hc : IsLabel F T a m c) (hd : IsLabel F T b n d)
    (k : ℕ) (e : Label.{uF, uV} F T k) :
    letI := T.topology
    letI := gradedInductionRing F T hx hl
    coeff F T k e (basisClass F T m c * basisClass F T n d) ≤
      coeff F T k e (zeta F T hx hl (a + b)) := by
  let := T.topology
  let := gradedInductionRing F T hx hl
  have ha := isEffective_sub_basisClass F T (isEffective_zeta F T hx hl a)
    (one_le_coeff_zeta_of_isLabel F T hx hl hc)
  have hb := isEffective_sub_basisClass F T (isEffective_zeta F T hx hl b)
    (one_le_coeff_zeta_of_isLabel F T hx hl hd)
  rw [zeta_add]
  refine (coeff_mul_le_mul_right F T hx hl ha (isEffective_basisClass F T n d) k e).trans ?_
  rw [mul_comm (zeta F T hx hl a), mul_comm (zeta F T hx hl a)]
  exact coeff_mul_le_mul_right F T hx hl hb (isEffective_zeta F T hx hl a) k e

include hl in
/-- Every socle label in a product is rank-lower than the sum of the two
factor multisegments. -/
theorem rankLE_of_coeff_mul_pos
    {a b q : T.Multisegment.{max uF uV, uF}} {m n k : ℕ}
    {c : Label.{uF, uV} F T m} {d : Label.{uF, uV} F T n}
    {e : Label.{uF, uV} F T k}
    (hc : IsLabel F T a m c) (hd : IsLabel F T b n d)
    (he : IsLabel F T q k e)
    (hpos : 0 < coeff F T k e
      (gradedMultiplication F T hx (basisClass F T m c) (basisClass F T n d))) :
    Multisegment.RankLE q (a + b) := by
  obtain ⟨ψ⟩ := HarmonicAnalysis.padicUnitaryAdditiveCharacterExists F T
  exact rankLE_of_coeff_zeta_pos F T hx hl ψ (highestDerivativeLabelStep F T ψ)
    k e q (a + b) he (hpos.trans_le (coeff_mul_le_zeta F T hx hl hc hd k e))

include hl in
/-- The coefficient of any label of `a` in its standard product is one. -/
theorem coeff_zeta_eq_one_of_isLabel
    {a : T.Multisegment.{max uF uV, uF}} {m : ℕ}
    {c : Label.{uF, uV} F T m} (hc : IsLabel F T a m c) :
    coeff F T m c (zeta F T hx hl a) = 1 := by
  obtain ⟨ψ⟩ := HarmonicAnalysis.padicUnitaryAdditiveCharacterExists F T
  have h := coeff_mul_le_weightedCount F T (labelWeight_nonneg F T a)
    (isEffective_zeta F T hx hl a) m c
  rw [labelWeight_of_isLabel F T hc, mul_one] at h
  exact le_antisymm
    (h.trans (labelCount_zeta_le_one F T hx hl ψ (highestDerivativeLabelStep F T ψ) a))
    (one_le_coeff_zeta_of_isLabel F T hx hl hc)

/-- Every label remaining after removing the leading class is strictly
rank-lower. -/
theorem rankLT_of_coeff_remainder_ne_zero
    {a q : T.Multisegment.{max uF uV, uF}} {m k : ℕ}
    {c : Label.{uF, uV} F T m} {e : Label.{uF, uV} F T k}
    (hc : IsLabel F T a m c) (he : IsLabel F T q k e)
    (hne : coeff F T k e (zeta F T hx hl a - basisClass F T m c) ≠ 0) :
    Multisegment.RankLE q a ∧ q ≠ a := by
  obtain ⟨ψ⟩ := HarmonicAnalysis.padicUnitaryAdditiveCharacterExists F T
  have hy := isEffective_sub_basisClass F T (isEffective_zeta F T hx hl a)
    (one_le_coeff_zeta_of_isLabel F T hx hl hc)
  have hpos : 0 < coeff F T k e (zeta F T hx hl a - basisClass F T m c) :=
    lt_of_le_of_ne (hy k e) (Ne.symm hne)
  have hz : 0 < coeff F T k e (zeta F T hx hl a) := by
    rw [map_sub] at hpos
    have := isEffective_basisClass F T m c k e
    omega
  refine ⟨rankLE_of_coeff_zeta_pos F T hx hl ψ (highestDerivativeLabelStep F T ψ)
    k e q a he hz, ?_⟩
  intro hqa
  have he' : IsLabel F T a k e := by simpa only [hqa] using he
  have hcount : weightedCount F T (labelWeight F T a)
      (zeta F T hx hl a - basisClass F T m c) ≤ 0 := by
    rw [map_sub, weightedCount_basisClass, labelWeight_of_isLabel F T hc]
    have := labelCount_zeta_le_one F T hx hl ψ (highestDerivativeLabelStep F T ψ) a
    omega
  have h := coeff_mul_le_weightedCount F T (labelWeight_nonneg F T a) hy k e
  rw [labelWeight_of_isLabel F T he', mul_one] at h
  omega

/-- A label of `a+b` cannot occur in the standard product of `q+b` when
`q` is strictly rank-lower than `a`. -/
theorem coeff_zeta_add_eq_zero_of_rankLT
    {a q b : T.Multisegment.{max uF uV, uF}} {k : ℕ}
    {e : Label.{uF, uV} F T k}
    (he : IsLabel F T (a + b) k e)
    (hq : Multisegment.RankLE q a) (hne : q ≠ a) :
    coeff F T k e (zeta F T hx hl (q + b)) = 0 := by
  by_contra hc
  obtain ⟨ψ⟩ := HarmonicAnalysis.padicUnitaryAdditiveCharacterExists F T
  have hpos := lt_of_le_of_ne (isEffective_zeta F T hx hl (q + b) k e) (Ne.symm hc)
  have hr := rankLE_of_coeff_zeta_pos F T hx hl ψ (highestDerivativeLabelStep F T ψ)
    k e (a + b) (q + b) he hpos
  have hh := (hq.add (.refl b)).antisymm hr
  exact hne (add_right_cancel hh)

/-- A linear functional vanishes when it vanishes on every basis class
with a nonzero coefficient. -/
theorem apply_eq_zero_of_coeff
    (χ : GradedGrothendieckGroup.{uF, uV} F T →ₗ[ℤ] ℤ)
    (x : GradedGrothendieckGroup.{uF, uV} F T)
    (h : ∀ m c, coeff F T m c x ≠ 0 → χ (basisClass F T m c) = 0) :
    χ x = 0 := by
  classical
  let := T.topology
  rw [apply_eq_sum F T χ x]
  refine Finset.sum_eq_zero fun m _ => Finset.sum_eq_zero fun c hc => ?_
  dsimp only
  rw [h m c (Finsupp.mem_support_iff.mp hc), mul_zero]

/-- The leading coefficient of the sum annihilates a strictly lower
remainder multiplied by any standard product. -/
theorem coeff_remainder_mul_zeta_eq_zero
    {a b : T.Multisegment.{max uF uV, uF}} {m k : ℕ}
    {c : Label.{uF, uV} F T m} {e : Label.{uF, uV} F T k}
    (hc : IsLabel F T a m c) (he : IsLabel F T (a + b) k e) :
    letI := T.topology
    letI := gradedInductionRing F T hx hl
    coeff F T k e ((zeta F T hx hl a - basisClass F T m c) * zeta F T hx hl b) = 0 := by
  let := T.topology
  let := gradedInductionRing F T hx hl
  apply apply_eq_zero_of_coeff F T
    ((coeff F T k e).comp ((gradedMultiplication F T hx).flip (zeta F T hx hl b)))
    (zeta F T hx hl a - basisClass F T m c)
  intro n d hd
  obtain ⟨q, hq⟩ := exists_isLabel F T (Classification.multisegmentSocleExhaustion F T) n d
  obtain ⟨hr, hne⟩ := rankLT_of_coeff_remainder_ne_zero F T hx hl hc hq hd
  have hbound := coeff_mul_le_mul_right F T hx hl
    (isEffective_sub_basisClass F T (isEffective_zeta F T hx hl q)
      (one_le_coeff_zeta_of_isLabel F T hx hl hq))
    (isEffective_zeta F T hx hl b) k e
  rw [← zeta_add, coeff_zeta_add_eq_zero_of_rankLT F T hx hl he hr hne] at hbound
  exact le_antisymm hbound (isEffective_mul F T hx hl
    (isEffective_basisClass F T n d) (isEffective_zeta F T hx hl b) k e)

/-- The label of the sum occurs exactly once in a product of two
irreducible socle labels. -/
theorem coeff_mul_eq_one
    {a b : T.Multisegment.{max uF uV, uF}} {m n k : ℕ}
    {c : Label.{uF, uV} F T m} {d : Label.{uF, uV} F T n}
    {e : Label.{uF, uV} F T k}
    (hc : IsLabel F T a m c) (hd : IsLabel F T b n d)
    (he : IsLabel F T (a + b) k e) :
    letI := T.topology
    letI := gradedInductionRing F T hx hl
    coeff F T k e (basisClass F T m c * basisClass F T n d) = 1 := by
  let := T.topology
  let := gradedInductionRing F T hx hl
  have ha := isEffective_sub_basisClass F T (isEffective_zeta F T hx hl a)
    (one_le_coeff_zeta_of_isLabel F T hx hl hc)
  have hb := isEffective_sub_basisClass F T (isEffective_zeta F T hx hl b)
    (one_le_coeff_zeta_of_isLabel F T hx hl hd)
  have hzeroa := coeff_remainder_mul_zeta_eq_zero F T hx hl hc he
  have he' : IsLabel F T (b + a) k e := by simpa only [add_comm] using he
  have hzerob := coeff_remainder_mul_zeta_eq_zero F T hx hl hd he'
  have hbound := coeff_mul_le_mul_right F T hx hl ha hb k e
  rw [mul_comm (zeta F T hx hl a), hzerob] at hbound
  have hminor : coeff F T k e
      (basisClass F T m c * (zeta F T hx hl b - basisClass F T n d)) = 0 :=
    le_antisymm hbound (isEffective_mul F T hx hl (isEffective_basisClass F T m c) hb k e)
  have hone := coeff_zeta_eq_one_of_isLabel F T hx hl he
  rw [zeta_add] at hone
  rw [sub_mul, map_sub] at hzeroa
  rw [mul_sub, map_sub] at hminor
  omega

end Langlands.Aubert.SocleProductLeadingTerm

namespace Langlands.Aubert

universe uF uV

/-- Products of actual Zelevinsky socle labels are rank triangular, and the
label of the sum multisegment occurs with multiplicity one. -/
theorem socleProductLeadingTerm {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
    (T : F.TopologicalData) : SocleProductLeadingTermStatement.{uF, uV} F T := by
  intro hx hl
  refine ⟨fun a b q m n k c d e hc hd he hpos =>
    SocleProductLeadingTerm.rankLE_of_coeff_mul_pos F T hx hl hc hd he hpos,
    fun a b m n k c d e hc hd he => ?_⟩
  exact SocleProductLeadingTerm.coeff_mul_eq_one F T hx hl hc hd he

end Langlands.Aubert
