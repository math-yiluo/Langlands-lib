import Langlands.Representation.Classification.TadicRectanglePrimeAlgebra
import Langlands.Representation.Classification.TadicRectanglePrimeRing
import Langlands.Representation.Classification.TadicRectanglePrimeCombinatorics
import Langlands.Representation.Classification.MultisegmentConstituentDataExistenceProof
import Langlands.Representation.Classification.OrderedMultisegmentSocleExistenceProof

/-!
# Tadić's Proposition 3.8: the classes `⟨a(n,d)^ρ⟩` are prime

In the monomial coordinates `ℤ[segments] ≅ R`, the class `X` of a Zelevinsky socle of the
rectangle `a₀ = a(n,d)^ρ` is a polynomial `Q` that is weighted homogeneous for the
segment-length weight, contains the monomial `X^{a₀} = X_{Δ_0} ⋯ X_{Δ_(n-1)}` with
coefficient one, and has degree at most one in each `X_{Δ_j}` (Tadić's Lemma 3.4). For each
adjacent pair `Δ_k, Δ_(k+1)` the monomial `X^{c_k}` of the multisegment `c_k` obtained by
replacing the pair by its union and intersection occurs in `Q`: its coefficient is minus
the number of labels of `c_k` in `ζ(a₀) - X`, and `ζ(a₀) - ζ(c_k)` is effective by
Zelevinsky's Proposition 4.6. The irreducibility criterion of
`TadicRectanglePrimeAlgebra` then shows that `Q` is prime.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace Langlands.Classification.TadicRectanglePrime

open Aubert Aubert.SegmentPolynomialSurjectivity PadicField.TopologicalData
open PadicField.TopologicalData.Multisegment
open SmoothRep SmoothRep.IrreducibleGrothendieckProof VirtualRepresentation

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

attribute [local instance] ringR

/-! ### Socles and labels -/

theorem isIrreducible_of_isZelevinskySocle {N : ℕ} {a : T.Multisegment.{max uF uV, uF}}
    {π : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear N F.Carrier)}
    (h : a.IsZelevinskySocle π) : letI := T.topology; π.IsIrreducible := by
  obtain ⟨d, -, -, -, hsoc⟩ := h
  exact hsoc.1

/-- A Zelevinsky socle of `a` is a label of `a`. -/
theorem isLabel_of_isZelevinskySocle {N : ℕ} {a : T.Multisegment.{max uF uV, uF}}
    {π : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear N F.Carrier)}
    (h : a.IsZelevinskySocle π) :
    letI := T.topology
    IsLabel F T a N (GeneralLinear.irreducibleIsoClass N F.Carrier π
      (isIrreducible_of_isZelevinskySocle F T h)) := by
  let := T.topology
  obtain ⟨d, hd, hz⟩ := h
  exact ⟨π, _, rfl, d, hd, hz.isZelevinskySubrepresentation⟩

/-- Every multisegment has a label. -/
theorem exists_isLabel_of (a : T.Multisegment.{max uF uV, uF}) :
    ∃ c : Label.{uF, uV} F T a.degree, IsLabel F T a a.degree c := by
  let := T.topology
  obtain ⟨⟨d, hd, ho, hs⟩, -⟩ := multisegmentConstituentDataExistence.{uF, uV} F T a
  obtain ⟨π, hπ⟩ := orderedMultisegmentSocleExistence.{uF, uV} F T _ d ho hs
  exact ⟨_, isLabel_of_isZelevinskySocle F T ⟨d, hd, hπ⟩⟩

/-! ### The neighbour `c_k` of the rectangle -/

theorem zetaR_add (a b : T.Multisegment.{max uF uV, uF}) :
    zetaR F T (a + b) = zetaR F T a * zetaR F T b :=
  zeta_add F T _ _ a b

/-- `ζ(a₀) - ζ(c_k)` is effective (Zelevinsky's Proposition 4.6 applied to the pair
`Δ_k, Δ_(k+1)`, multiplied by `ζ` of the remaining segments). -/
theorem isEffective_zetaR_rect_sub_adj (σ : T.CuspidalDatum.{max uF uV, uF}) {n k : ℕ}
    (e : ℕ) (hk : k + 1 < n) :
    IsEffective F T (zetaR F T (rect σ n e) - zetaR F T (adj σ n k e)) := by
  obtain ⟨U, I, hrep, heff⟩ :=
    exists_isEffective_zetaR_pair_sub F T (seg_precedes (σ := σ) k e)
  rw [replacement_eq hrep] at heff
  rw [rect_eq_pair_add e hk, adj_eq_add, zetaR_add, zetaR_add, ← sub_mul]
  exact isEffective_mul F T heff (isEffective_zeta F T _ _ _)

open Classical in
/-- The monomial `X^{c_k}` occurs in the polynomial of a label of the rectangle. -/
theorem coeff_poly_adj_ne_zero (σ : T.CuspidalDatum.{max uF uV, uF}) {n k : ℕ} (e : ℕ)
    (hk : k + 1 < n) {m : ℕ} {c : Label.{uF, uV} F T m} (hc : IsLabel F T (rect σ n e) m c) :
    (poly F T (basisClass F T m c)).coeff (Multiset.toFinsupp (adj σ n k e)) ≠ 0 := by
  set Y := zetaR F T (rect σ n e) - basisClass F T m c with hY
  have hYeff : IsEffective F T Y := isEffective_zetaR_sub_basisClass F T hc
  have he : poly F T (basisClass F T m c) =
      MvPolynomial.monomial (Multiset.toFinsupp (rect σ n e)) 1 - poly F T Y := by
    have h1 : poly F T Y = poly F T (zetaR F T (rect σ n e)) - poly F T (basisClass F T m c) :=
      map_sub (segmentEquiv F T).symm _ _
    rw [h1, poly_zetaR, sub_sub_cancel]
  have hne : Multiset.toFinsupp (rect σ n e) ≠ Multiset.toFinsupp (adj σ n k e) := fun h =>
    adj_ne_rect e hk (Multiset.toFinsupp.injective h).symm
  rw [he, MvPolynomial.coeff_sub, MvPolynomial.coeff_monomial, ite_eq_right hne, zero_sub,
    neg_ne_zero, ← polyCoeff_apply]
  -- The coefficient of `X^{c_k}` in `Y` counts the labels of `c_k` in `Y`.
  have hφ : polyCoeff F T (Multiset.toFinsupp (adj σ n k e)) Y =
      weightedCount F T (labelWeight F T (adj σ n k e)) Y := by
    refine apply_eq_of_coeff F T fun m' c' hc' => ?_
    rw [weightedCount_basisClass, polyCoeff_apply]
    obtain ⟨b', hb'⟩ := exists_isLabel F T (multisegmentSocleExhaustion F T) m' c'
    have hpos : 0 < coeff F T m' c' Y := lt_of_le_of_ne (hYeff m' c') (Ne.symm hc')
    have hz : 0 < coeff F T m' c' (zetaR F T (rect σ n e)) := by
      have := isEffective_basisClass F T m c m' c'
      rw [hY, map_sub] at hpos
      omega
    have hrank : RankLE b' (rect σ n e) := rankLE_of_isLabel_of_coeff_pos F T hb' hz
    have hne' : b' ≠ rect σ n e := by
      rintro rfl
      have := coeff_zetaR_sub_basisClass_eq_zero F T hc hb'
      rw [← hY] at this
      omega
    by_cases hL : IsLabel F T (adj σ n k e) m' c'
    · rw [labelWeight_of_isLabel F T hL]
      exact (poly_basisClass F T _ m' c' hL).1
    · rw [labelWeight_of_not_isLabel F T hL]
      by_contra hμ
      have h1 := (poly_basisClass F T b' m' c' hb').2 _ hμ
      rw [Multiset.toFinsupp_toMultiset] at h1
      rw [← eq_adj_of_rankLE e hk h1 hrank hne'] at hL
      exact hL hb'
  rw [hφ]
  obtain ⟨L, hL⟩ := exists_isLabel_of F T (adj σ n k e)
  have hwY : weightedCount F T (labelWeight F T (adj σ n k e)) Y =
      weightedCount F T (labelWeight F T (adj σ n k e)) (zetaR F T (rect σ n e)) := by
    rw [hY, map_sub, weightedCount_basisClass, labelWeight_of_not_isLabel F T
      (fun h => adj_ne_rect e hk (eq_of_isLabel F T h hc)), sub_zero]
  have h1 := weightedCount_nonneg F T (labelWeight_nonneg F T (adj σ n k e))
    (isEffective_zetaR_rect_sub_adj F T σ e hk)
  rw [map_sub] at h1
  have h2 : coeff F T _ L (zetaR F T (adj σ n k e)) * labelWeight F T (adj σ n k e) _ L ≤
      weightedCount F T (labelWeight F T (adj σ n k e)) (zetaR F T (adj σ n k e)) :=
    coeff_mul_le_weightedCount F T (labelWeight_nonneg F T _) (isEffective_zeta F T _ _ _) _ L
  rw [labelWeight_of_isLabel F T hL, mul_one] at h2
  have h3 : 1 ≤ coeff F T _ L (zetaR F T (adj σ n k e)) :=
    one_le_coeff_zeta_of_isLabel F T _ _ hL
  omega

/-! ### Primality -/

open Classical in
/-- **Tadić 1986, Proposition 3.8, for a label.** The class of a label of the rectangle
`rect σ n e` (`n > 0`) is prime in `R`. -/
theorem prime_basisClass_rect (σ : T.CuspidalDatum.{max uF uV, uF}) {n : ℕ} (hn : 0 < n)
    (e : ℕ) {m : ℕ} {c : Label.{uF, uV} F T m} (hc : IsLabel F T (rect σ n e) m c) :
    Prime (basisClass F T m c) := by
  have htri := poly_basisClass F T (rect σ n e) m c hc
  rw [← (segmentEquiv F T).apply_symm_apply (basisClass F T m c), MulEquiv.prime_iff]
  refine prime_of_adjacent (fun j => seg σ j e) n (fun S : T.Segment.{max uF uV, uF} => S.length)
    (fun S => S.length_pos) (W := Multiset.card (rect σ n e).cuspidalContent) ?_ hn
    (fun i _ j _ h => seg_injective e h) (D := e + 1) (fun _ _ => rfl) ?_ ?_ ?_
  · intro μ hμ
    have hr := htri.2 μ hμ
    rw [← Finsupp.toMultiset_toFinsupp μ, weight_toFinsupp, hr.1]
  · rw [← toFinsupp_rect]
    exact htri.1
  · intro μ hμ j _
    have h := count_le_one_of_rankLE (htri.2 μ hμ) j
    rwa [Finsupp.count_toMultiset] at h
  · intro k hk
    refine ⟨Multiset.toFinsupp (adj σ n k e), coeff_poly_adj_ne_zero F T σ e hk hc, ?_, ?_,
      fun j hj hjk hjk1 => ?_, fun ν hν h0 => weight_ne_of_le_adj e hν h0⟩
    · rw [Multiset.toFinsupp_apply, count_adj_left]
    · rw [Multiset.toFinsupp_apply, count_adj_right]
    · rw [Multiset.toFinsupp_apply, count_adj_of_ne e hj hjk hjk1]

/-- **Tadić 1986, Proposition 3.8.** The class in `R` of every Zelevinsky socle of
`a(n,d)^ρ` is a prime element. -/
theorem tadicRectangleSoclePrime : TadicRectangleSoclePrime.{uF, uV} F T := by
  let := T.topology
  intro ρ n d hd hn N π hsoc hπ
  have hirr := isIrreducible_of_isZelevinskySocle F T hsoc
  have hc : IsLabel F T (tadicMultisegment ρ n d hd) N
      (GeneralLinear.irreducibleIsoClass N F.Carrier π hirr) :=
    isLabel_of_isZelevinskySocle F T hsoc
  rw [tadicMultisegment_eq_rect] at hc
  have h := prime_basisClass_rect F T _ hn (d - 1) hc
  rwa [basisClass_irreducibleIsoClass] at h

end Langlands.Classification.TadicRectanglePrime
