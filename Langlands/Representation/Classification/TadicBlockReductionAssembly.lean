import Langlands.Representation.Classification.TadicBlockBlocks
import Langlands.Representation.Classification.TadicBlockDerivative
import Langlands.Representation.Classification.TadicBlockReductionStatement
import Langlands.Representation.Classification.MultisegmentSocleExhaustionProof

/-!
# Assembly of Tadić's Lemma 4.8(ii) from its inputs

The induction proving `TadicBlockReductionFromInputs`: Tadić's Lemma 4.8(ii) from Bernstein's
Theorem 2.5(i),(iii), Tadić's Propositions 2.9 and 3.8, Zelevinsky's Proposition 8.5 and the
Hermitian symmetry of unitarizable representations.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace Langlands.Classification.TadicBlockReductionAssembly

open Aubert Aubert.SegmentPolynomialSurjectivity PadicField.TopologicalData GeneralLinear
open TadicBlockRing TadicBlockCombinatorics TadicBlockBlocks TadicBlockDerivative

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

attribute [local instance] ringR

/-! ### Algebraic helpers -/

/-- A divisor of a product of primes is associated to a sub-product (indexed form). -/
theorem exists_le_associated_of_dvd_prod_map {M₀ ι : Type*} [CommMonoidWithZero M₀]
    [IsCancelMulZero M₀] (J : Multiset ι) (f : ι → M₀) (hf : ∀ i ∈ J, Prime (f i)) {x : M₀}
    (h : x ∣ (J.map f).prod) : ∃ J' ≤ J, Associated x (J'.map f).prod := by
  induction J using Multiset.induction_on generalizing x with
  | empty =>
    rw [Multiset.map_zero, Multiset.prod_zero] at h
    refine ⟨0, le_rfl, ?_⟩
    rw [Multiset.map_zero, Multiset.prod_zero]
    exact associated_one_iff_isUnit.mpr (isUnit_of_dvd_one h)
  | cons i J ih =>
    have hq : Prime (f i) := hf i (Multiset.mem_cons_self i J)
    have hs' : ∀ j ∈ J, Prime (f j) := fun j hj => hf j (Multiset.mem_cons_of_mem hj)
    rw [Multiset.map_cons, Multiset.prod_cons] at h
    by_cases hqx : f i ∣ x
    · obtain ⟨y, rfl⟩ := hqx
      have hy : y ∣ (J.map f).prod := (mul_dvd_mul_iff_left hq.ne_zero).mp h
      obtain ⟨t, hts, hyt⟩ := ih hs' hy
      refine ⟨i ::ₘ t, Multiset.cons_le_cons i hts, ?_⟩
      rw [Multiset.map_cons, Multiset.prod_cons]
      exact hyt.mul_left (f i)
    · obtain ⟨c, hc⟩ := h
      have hqc : f i ∣ c := by
        rcases hq.dvd_or_dvd (Dvd.intro _ hc) with h1 | h1
        · exact absurd h1 hqx
        · exact h1
      obtain ⟨c', rfl⟩ := hqc
      have hx : x ∣ (J.map f).prod := by
        refine ⟨c', ?_⟩
        have : f i * (J.map f).prod = f i * (x * c') := by rw [hc, mul_left_comm]
        exact mul_left_cancel₀ hq.ne_zero this
      obtain ⟨t, hts, hxt⟩ := ih hs' hx
      exact ⟨t, hts.trans (Multiset.le_cons_self J i), hxt⟩

theorem prod_map_finset_sum {ι : Type*} (s : Finset ι)
    (J : ι → Multiset (RParam.{uF, max uF uV} T)) :
    (((∑ i ∈ s, J i).map (rectCls F T)).prod) = ∏ i ∈ s, ((J i).map (rectCls F T)).prod := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s his ih =>
    rw [Finset.sum_insert his, Finset.prod_insert his, Multiset.map_add, Multiset.prod_add, ih]

theorem UFamily.zero : UFamily F T (0 : Multiset (RParam.{uF, max uF uV} T)) :=
  ⟨fun q hq => absurd hq (Multiset.notMem_zero q), rfl, fun q hq => absurd hq (Multiset.notMem_zero q)⟩

theorem UFamily.finset_sum {ι : Type*} (s : Finset ι)
    (J : ι → Multiset (RParam.{uF, max uF uV} T)) (h : ∀ i ∈ s, UFamily F T (J i)) :
    UFamily F T (∑ i ∈ s, J i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact UFamily.zero F T
  | insert i s his ih =>
    rw [Finset.sum_insert his]
    exact (h i (Finset.mem_insert_self i s)).add F T
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem tadicSocleUnitarity_mono {j k : ℕ} (hjk : j ≤ k)
    (h : TadicSocleUnitarity.{uF, uV} F T k) : TadicSocleUnitarity.{uF, uV} F T j := by
  intro ρ n d hd hn hρ N σ hN hσ
  exact h ρ n d hd hn hρ σ (hN.trans hjk) hσ

/-- One-element rectangle families are unitary families (Steinberg-type representations). -/
theorem uFamily_of_stFamily {J : Multiset (RParam.{uF, max uF uV} T)} (h : StFamily J) :
    UFamily F T J := by
  refine ⟨fun q hq => (h.1 q hq).1, h.2, fun q hq => ?_⟩
  obtain ⟨hv, hd1⟩ := h.1 q hq
  intro N X hX
  obtain ⟨ρ, n, d, hd, α⟩ := q
  simp only at hd1 hX
  subst hd1
  exact TadicBlockSteinberg.isUnitarizable_of_isZelevinskySocle_one hv.1 hv.2.1 hX

theorem RParam.ext_refl (q : RParam.{uF, max uF uV} T) : q.ext.refl = q.refl.ext := rfl

/-! ### Degrees -/

theorem degree_rect_le_sum {J : Multiset (RParam.{uF, max uF uV} T)} {q : RParam.{uF, max uF uV} T}
    (hq : q ∈ J) : q.rect.degree ≤ (J.map RParam.rect).sum.degree := by
  rw [degree_sum_rect]
  exact Multiset.le_sum_of_mem
    (Multiset.mem_map_of_mem (fun r : RParam.{uF, max uF uV} T => r.rect.degree) hq)

theorem degree_rect_refl (q : RParam.{uF, max uF uV} T) : q.refl.rect.degree = q.rect.degree := by
  rw [degree_rect, degree_rect]
  rfl

theorem rect_degree_pos {q : RParam.{uF, max uF uV} T} (hv : q.Valid) : 0 < q.rect.degree := by
  rw [degree_rect]
  exact baseDegree_pos F T q hv

/-- In an admissible reflection-invariant family of total degree at most `m + 1`, every
rectangle has degree at most `m`, unless it is a single rectangle with `α = 0` of degree
`m + 1`. -/
theorem base_degree_le {J : Multiset (RParam.{uF, max uF uV} T)}
    (hrefl : J.map RParam.refl = J) {m : ℕ}
    (hdeg : (J.map RParam.rect).sum.degree ≤ m + 1)
    (hex : ∀ q ∈ J, q.α = 0 → q.rect.degree = m + 1 → False) :
    ∀ q ∈ J, (tadicMultisegment q.ρ q.n q.d q.hd).degree ≤ m := by
  classical
  intro q hq
  rw [← degree_rect]
  have h1 := (degree_rect_le_sum F T hq).trans hdeg
  by_contra hlt
  have hq1 : q.rect.degree = m + 1 := by omega
  by_cases hα : q.α = 0
  · exact hex q hq hα hq1
  · have hmem : q.refl ∈ J := by
      rw [← hrefl]; exact Multiset.mem_map_of_mem _ hq
    have hne : q.refl ≠ q := by
      intro h
      apply hα
      have := congrArg RParam.α h
      simp only [RParam.refl_α] at this
      linarith
    have hmem' : q.refl ∈ J.erase q := (Multiset.mem_erase_of_ne hne).mpr hmem
    have hsplit := Multiset.cons_erase hq
    have h2 : q.rect.degree + q.refl.rect.degree ≤ (J.map RParam.rect).sum.degree := by
      conv_rhs => rw [← hsplit]
      rw [Multiset.map_cons, Multiset.sum_cons]
      have := degree_rect_le_sum F T hmem'
      simp only [Multisegment.degree, Multiset.map_add, Multiset.sum_add] at this ⊢
      omega
    rw [degree_rect_refl] at h2
    omega

/-- A rectangle of the full degree contained in `a` is `a`. -/
theorem eq_of_le_of_degree_eq {a b : T.Multisegment.{max uF uV, uF}} (h : b ≤ a)
    (hd : b.degree = a.degree) : a = b := by
  obtain ⟨c, rfl⟩ := Multiset.le_iff_exists_add.mp h
  have hc : Multisegment.degree c = 0 := by
    have : Multisegment.degree (b + c) = b.degree + Multisegment.degree c := by
      simp [Multisegment.degree, Multiset.map_add, Multiset.sum_add]
    omega
  rw [eq_zero_of_degree_eq_zero F T hc, add_zero]

theorem rect_le_sum {J : Multiset (RParam.{uF, max uF uV} T)} {q : RParam.{uF, max uF uV} T}
    (hq : q ∈ J) : q.rect ≤ (J.map RParam.rect).sum :=
  Multiset.le_sum_of_mem (Multiset.mem_map_of_mem _ hq)

/-! ### Products with an extra factor -/

/-- If the class of an irreducible `X` is `[π] ∏ [⟨rect q⟩]` for a socle `π` of `a`, then
`X` is a socle of `a + ∑ rect q`. -/
theorem isZelevinskySocle_of_cls_eq_mul_prod {N N₀ : ℕ}
    {X : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear N F.Carrier)}
    (hX : letI := T.topology; X.IsIrreducible) (hXf : letI := T.topology; X.HasFiniteLength)
    {π : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear N₀ F.Carrier)}
    {a : T.Multisegment.{max uF uV, uF}} (ha : a.IsZelevinskySocle π)
    (hπf : letI := T.topology; π.HasFiniteLength) (J : Multiset (RParam.{uF, max uF uV} T))
    (h : cls F T X hXf = cls F T π hπf * (J.map (rectCls F T)).prod) :
    (a + (J.map RParam.rect).sum).IsZelevinskySocle X := by
  let := T.topology
  obtain ⟨τ, hτ⟩ := exists_isZelevinskySocle F T (a + (J.map RParam.rect).sum)
  have hL := isLabel_of_isZelevinskySocle F T hτ
  have hπi := isIrreducible_of_isZelevinskySocle F T ha
  have hlπ := isLabel_of_isZelevinskySocle F T ha
  obtain ⟨Ls, hLs⟩ := exists_isLabel_of F T (J.map RParam.rect).sum
  have hih := one_le_coeff_prod_rectCls F T J hLs
  have hE : IsEffective F T ((J.map (rectCls F T)).prod - basisClass F T _ Ls) :=
    isEffective_sub_basisClass F T (isEffective_prod_rectCls F T J) hih
  have hπc := cls_eq_basisClass F T hπi hπf
  have e : cls F T π hπf * (J.map (rectCls F T)).prod =
      cls F T π hπf * basisClass F T _ Ls +
        cls F T π hπf * ((J.map (rectCls F T)).prod - basisClass F T _ Ls) := by ring
  have h1 := one_le_coeff_basisClass_mul F T hlπ hLs hL
  rw [← hπc] at h1
  have hπe : IsEffective F T (cls F T π hπf) := by
    rw [hπc]; exact isEffective_basisClass F T _ _
  have h2 := isEffective_mul F T hπe hE _
    (GeneralLinear.irreducibleIsoClass _ F.Carrier τ (isIrreducible_of_isZelevinskySocle F T hτ))
  have h3 : 1 ≤ coeff F T _ (GeneralLinear.irreducibleIsoClass _ F.Carrier τ
      (isIrreducible_of_isZelevinskySocle F T hτ)) (cls F T X hXf) := by
    rw [h, e, map_add]
    omega
  rw [cls_eq_basisClass F T hX] at h3
  by_cases hN : (a + (J.map RParam.rect).sum).degree = N
  · subst hN
    by_cases hc' : GeneralLinear.irreducibleIsoClass _ F.Carrier X hX =
        GeneralLinear.irreducibleIsoClass _ F.Carrier τ (isIrreducible_of_isZelevinskySocle F T hτ)
    · obtain ⟨e'⟩ := (SmoothRep.irreducibleIsoClass_eq_iff hX _).mp hc'
      exact Multisegment.IsZelevinskySocle.of_iso hτ e'.symm
    · rw [coeff_basisClass_of_ne F T _ hc'] at h3
      omega
  · rw [basisClass, coeff_gradedInclusion_of_ne F T hN] at h3
    omega


/-! ### The induction -/

/-- Lemma 4.8(ii) at one rank `m + 1`. -/
def BlockReductionAt (m : ℕ) : Prop :=
  letI := T.topology
  TadicSocleUnitarity.{uF, uV} F T m →
    ∀ π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (m + 1) F.Carrier),
      Representation.IsIrreducible π.representation → IsUnitarizable π.representation →
      (¬ ∃ (ρ : T.CuspidalDatum.{max uF uV, uF}) (n d : ℕ) (hd : 0 < d),
          0 < n ∧ ρ.IsUnitary ∧ (tadicMultisegment ρ n d hd).IsZelevinskySocle π) →
      ∃ (B : BlockShape (m + 1))
        (σ : ∀ i, SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (B.size i) F.Carrier)),
        (∀ i, IsTadicXBlock m (σ i)) ∧
          Nonempty (π ≅ (T.normalizedProductInductionFunctor B).obj σ)

theorem tadicBlockReduction_iff :
    TadicBlockReduction.{uF, uV} F T ↔ ∀ m, BlockReductionAt.{uF, uV} F T m :=
  Iff.rfl

/-- Two socles of an irreducible `π` determine the same multisegment. -/
theorem eq_of_isZelevinskySocle {N : ℕ}
    {π : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear N F.Carrier)}
    {a b : T.Multisegment.{max uF uV, uF}} (ha : a.IsZelevinskySocle π)
    (hb : b.IsZelevinskySocle π) : a = b :=
  eq_of_isLabel F T (isLabel_of_isZelevinskySocle F T ha) (isLabel_of_isZelevinskySocle F T hb)

/-- The multisegment `ν^(1/2) a⁻` of the shifted highest derivative of a unitarizable `⟨a⟩`
is a sum of admissible rectangles of a unitary family (by the induction hypothesis). -/
theorem exists_derivative_family (hA : BernsteinUnitaryProductIrreducibility.{uF, uV} F T)
    (hB3 : BernsteinShiftedHighestDerivativeUnitarity.{uF, uV} F T)
    (hD : UnlinkedSocleProductIrreducibility.{uF, uV} F T) {m : ℕ}
    (ih : ∀ m' < m, BlockReductionAt.{uF, uV} F T m') (hU : TadicSocleUnitarity.{uF, uV} F T m)
    (π : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (m + 1) F.Carrier))
    (hirr : letI := T.topology; Representation.IsIrreducible π.representation)
    (hu : letI := T.topology; IsUnitarizable π.representation)
    {a : T.Multisegment.{max uF uV, uF}} (ha : a.IsZelevinskySocle π) :
    ∃ J : Multiset (RParam.{uF, max uF uV} T), UFamily F T J ∧
      (Multisegment.dropLast a).twist (1 / 2) = (J.map RParam.rect).sum := by
  let := T.topology
  obtain ⟨M, π', hMlt, hirr', hu', hdegM, hsoc'⟩ :=
    exists_shiftedHighestDerivative_socle F T hB3 (Nat.succ_pos m) π hirr hu ha
  by_cases hM : M = 0
  · subst hM
    have h0 := eq_zero_of_degree_eq_zero F T hdegM
    refine ⟨0, UFamily.zero F T, ?_⟩
    rw [h0]
    rfl
  obtain ⟨M', rfl⟩ : ∃ M', M = M' + 1 := ⟨M - 1, by omega⟩
  have hsoc := hsoc' (Nat.succ_pos M')
  have hfl := SmoothRep.hasFiniteLength_of_isIrreducible hirr'
  have key : ∃ J : Multiset (RParam.{uF, max uF uV} T), UFamily F T J ∧
      cls F T π' hfl = (J.map (rectCls F T)).prod := by
    by_cases hX : ∃ (ρ : T.CuspidalDatum.{max uF uV, uF}) (n d : ℕ) (hd : 0 < d),
        0 < n ∧ ρ.IsUnitary ∧ (tadicMultisegment ρ n d hd).IsZelevinskySocle π'
    · obtain ⟨ρ, n, d, hd, hn, hρ, hs⟩ := hX
      obtain ⟨hirr0, J, hJ, hcls⟩ := isTadicXBlock_analysis F T hA hD hU
        (Or.inl ⟨ρ, n, d, hd, hn, hρ, by omega, hs⟩)
      exact ⟨J, hJ, hcls⟩
    · have hU' := tadicSocleUnitarity_mono F T (show M' ≤ m by omega) hU
      obtain ⟨B, σ, hσX, ⟨e⟩⟩ := ih M' (by omega) hU' π' hirr' hu' hX
      have han := fun i => isTadicXBlock_analysis F T hA hD hU' (hσX i)
      choose hirri J hJ hcls using han
      refine ⟨∑ i, J i, UFamily.finset_sum F T _ J fun i _ => hJ i, ?_⟩
      rw [prod_map_finset_sum, cls_eq_of_iso F T e hfl (hasFiniteLength_product F T B σ hirri),
        cls_product F T B σ hirri]
      exact Finset.prod_congr rfl fun i _ => hcls i
  obtain ⟨J, hJ, hcls⟩ := key
  refine ⟨J, hJ, eq_of_isZelevinskySocle F T hsoc ?_⟩
  exact isZelevinskySocle_of_cls_eq_prod_rectCls F T hirr' hfl J hcls

/-- Under the hypothesis of Lemma 4.8(ii), `⟨a⟩` is not a single rectangle with `α = 0`. -/
theorem not_rect_eq {N : ℕ}
    {π : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear N F.Carrier)}
    (hnot : ¬ ∃ (ρ : T.CuspidalDatum.{max uF uV, uF}) (n d : ℕ) (hd : 0 < d),
          0 < n ∧ ρ.IsUnitary ∧ (tadicMultisegment ρ n d hd).IsZelevinskySocle π)
    {a : T.Multisegment.{max uF uV, uF}} (ha : a.IsZelevinskySocle π)
    {q : RParam.{uF, max uF uV} T} (hv : q.Valid) (hα : q.α = 0) (hle : q.rect ≤ a)
    (hdeg : q.rect.degree = a.degree) : False := by
  have he := eq_of_le_of_degree_eq F T hle hdeg
  rw [he] at ha
  change (tadicMultisegment (q.ρ.twist q.α) q.n q.d q.hd).IsZelevinskySocle π at ha
  rw [hα, CuspidalDatum.twist_zero] at ha
  exact hnot ⟨q.ρ, q.n, q.d, q.hd, hv.2.1, hv.1, ha⟩

/-- Base unitarity from `(U^m)` once the base degree is at most `m`. -/
theorem baseUnitary_of_le {m : ℕ} (hU : TadicSocleUnitarity.{uF, uV} F T m)
    {q : RParam.{uF, max uF uV} T} (hv : q.Valid)
    (hq : (tadicMultisegment q.ρ q.n q.d q.hd).degree ≤ m) : BaseUnitary F T q := by
  intro N X hX
  have h1 := tadicMultisegment_rank_eq_of_isZelevinskySocle hX
  rw [tadicMultisegment_degree] at hq
  exact hU q.ρ q.n q.d q.hd hv.2.1 hv.1 X (by omega) hX

theorem map_sum_rect_extSeg (J : Multiset (RParam.{uF, max uF uV} T)) :
    ((J.map RParam.rect).sum).map extSeg = ((J.map RParam.ext).map RParam.rect).sum := by
  induction J using Multiset.induction_on with
  | empty => simp
  | cons q J ih =>
    rw [Multiset.map_cons, Multiset.sum_cons, Multiset.map_add, ih, RParam.rect_map_extSeg,
      Multiset.map_cons, Multiset.map_cons, Multiset.sum_cons]


theorem degree_le_of_le {a b : T.Multisegment.{max uF uV, uF}} (h : b ≤ a) :
    b.degree ≤ a.degree := by
  obtain ⟨c, rfl⟩ := Multiset.le_iff_exists_add.mp h
  have : Multisegment.degree (b + c) = b.degree + Multisegment.degree c := by
    simp [Multisegment.degree, Multiset.map_add, Multiset.sum_add]
  omega

/-- **The induction step**: Lemma 4.8(ii) at rank `m + 1` from all smaller ranks. -/
theorem step (hin : TadicBlockReductionInputs.{uF, uV} F T) (m : ℕ)
    (ih : ∀ m' < m, BlockReductionAt.{uF, uV} F T m') : BlockReductionAt.{uF, uV} F T m := by
  classical
  let := T.topology
  obtain ⟨hA, hB3, hC, hD, hE, hF⟩ := hin
  intro hU π hirr hu hnot
  -- the multisegment of `π`
  obtain ⟨a, hadeg, ha⟩ := multisegmentSocleExhaustion.{uF, uV} F T (m + 1) π hirr
  -- the family given by the shifted highest derivative
  obtain ⟨JX, hJX, hJXsum⟩ := exists_derivative_family F T hA hB3 hD ih hU π hirr hu ha
  set JXe := JX.map RParam.ext with hJXe_def
  set φ := a.filter (fun Δ => Δ.length = 1) with hφ_def
  have hadec : a = (JXe.map RParam.rect).sum + φ := by
    conv_lhs => rw [eq_extSeg_dropLast_add a]
    rw [hJXsum, map_sum_rect_extSeg]
  have hJXe_valid : ∀ q ∈ JXe, q.Valid := by
    intro q hq
    obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.mp hq
    exact hJX.valid r hr
  have hJXe_refl : JXe.map RParam.refl = JXe := by
    rw [hJXe_def, Multiset.map_map]
    conv_rhs => rw [← hJX.refl]
    rw [Multiset.map_map]
    rfl
  -- Hermitian symmetry
  have harefl : a.map reflSeg = a :=
    map_reflSeg_eq_of_count fun ρ hρ x l hl => hF π a hirr hu ha ρ hρ x l hl
  have hφrefl : φ.map reflSeg = φ := by
    have h1 := harefl
    rw [hadec, Multiset.map_add, ← sum_rect_map_refl hJXe_valid, hJXe_refl] at h1
    exact add_left_cancel h1
  -- the one-element segments
  obtain ⟨L, R, hL, hR, hLR⟩ := onePoint_decomposition _ φ rfl
    (fun Δ hΔ => (Multiset.mem_filter.mp hΔ).2) hφrefl
  -- `⟨a⟩` is not a single rectangle
  have hex : ∀ J : Multiset (RParam.{uF, max uF uV} T), (J.map RParam.rect).sum ≤ a →
      ∀ q ∈ J, q.Valid → q.α = 0 → q.rect.degree = m + 1 → False := by
    intro J hJa q hq hv hα hdeg
    exact not_rect_eq F T hnot ha hv hα ((rect_le_sum F T hq).trans hJa) (by rw [hdeg, hadeg])
  -- the family `JXe` is unitary
  have hle : (JXe.map RParam.rect).sum ≤ a := by
    rw [hadec]; exact Multiset.le_add_right _ _
  have hbX := base_degree_le F T hJXe_refl
    ((degree_le_of_le F T hle).trans hadeg.le)
    (fun q hq hα hd => hex _ hle q hq (hJXe_valid q hq) hα hd)
  have hJXeU : UFamily F T JXe :=
    ⟨hJXe_valid, hJXe_refl, fun q hq => baseUnitary_of_le F T hU (hJXe_valid q hq) (hbX q hq)⟩
  have hLU := uFamily_of_stFamily F T hL
  have hRU := uFamily_of_stFamily F T hR
  have hJRU := hJXeU.add F T hRU
  -- the two products `π × ∏ L` and `∏ (JXe + R)`
  let πB : UIrr.{uF, uV} F T := ⟨m + 1, Nat.succ_pos m, π, hirr, hu⟩
  let lL := πB :: famBlocks F T hA hC hD L hLU
  let lR := famBlocks F T hA hC hD (JXe + R) hJRU
  obtain ⟨hXLi, -⟩ := listProduct_irr_unit F T hA lL rfl
  obtain ⟨hXRi, -⟩ := listProduct_irr_unit F T hA lR rfl
  have hXLf := SmoothRep.hasFiniteLength_of_isIrreducible hXLi
  have hXRf := SmoothRep.hasFiniteLength_of_isIrreducible hXRi
  have hπf := SmoothRep.hasFiniteLength_of_isIrreducible hirr
  have hclsL : cls F T (listProduct F T lL rfl) hXLf =
      cls F T π hπf * (L.map (rectCls F T)).prod := by
    rw [cls_listProduct, List.map_cons, List.prod_cons, famBlocks_cl]
    rfl
  have hclsR : cls F T (listProduct F T lR rfl) hXRf = ((JXe + R).map (rectCls F T)).prod := by
    rw [cls_listProduct, famBlocks_cl]
  have hsL := isZelevinskySocle_of_cls_eq_mul_prod F T hXLi hXLf ha hπf L hclsL
  have hsR := isZelevinskySocle_of_cls_eq_prod_rectCls F T hXRi hXRf (JXe + R) hclsR
  have hmseg : a + (L.map RParam.rect).sum = ((JXe + R).map RParam.rect).sum := by
    rw [hadec, Multiset.map_add, Multiset.sum_add, add_assoc, hLR]
  rw [hmseg] at hsL
  have hclsEq : cls F T π hπf * (L.map (rectCls F T)).prod =
      ((JXe + R).map (rectCls F T)).prod := by
    rw [← hclsL, ← hclsR]
    exact cls_eq_of_isZelevinskySocle F T hsL hsR _ _
  -- Tadić's Proposition 3.8 and unique factorization
  have hprime : ∀ q ∈ JXe + R, Prime (rectCls F T q) := by
    intro q hq
    have hv := hJRU.valid q hq
    exact hE (q.ρ.twist q.α) q.n q.d q.hd hv.2.1 (rectSocle F T q) (rectSocle_spec F T q) _
  have := isDomain_R F T
  obtain ⟨J, hJle, hassoc⟩ := exists_le_associated_of_dvd_prod_map (JXe + R) (rectCls F T)
    hprime (Dvd.intro _ hclsEq)
  have hπcls : cls F T π hπf = (J.map (rectCls F T)).prod := by
    rcases eq_or_eq_neg_of_associated F T hassoc with h | h
    · exact h
    · exfalso
      have h1 := congrArg (coeff F T (m + 1) (GeneralLinear.irreducibleIsoClass _ F.Carrier π hirr))
        h
      rw [cls_eq_basisClass F T hirr, coeff_basisClass_self, map_neg] at h1
      have h2 := isEffective_prod_rectCls F T J (m + 1)
        (GeneralLinear.irreducibleIsoClass _ F.Carrier π hirr)
      omega
  -- `a` is the sum of the rectangles of `J`, and `J` is reflection invariant
  have hsJ := isZelevinskySocle_of_cls_eq_prod_rectCls F T hirr hπf J hπcls
  have haJ : a = (J.map RParam.rect).sum := eq_of_isZelevinskySocle F T ha hsJ
  have hJvalid : ∀ q ∈ J, q.Valid := fun q hq => hJRU.valid q (Multiset.mem_of_le hJle hq)
  have hJrefl : J.map RParam.refl = J := map_refl_eq_of_sum hJvalid (by rw [← haJ]; exact harefl)
  have hb := base_degree_le F T hJrefl (by rw [← haJ, hadeg])
    (fun q hq hα hd => hex J (le_of_eq haJ.symm) q hq (hJvalid q hq) hα hd)
  have hJU : UFamily F T J :=
    ⟨hJvalid, hJrefl, fun q hq => baseUnitary_of_le F T hU (hJvalid q hq) (hb q hq)⟩
  -- the factorization
  let lF := famBlocks F T hA hC hD J hJU
  have hN : (lF.map UIrr.N).sum = m + 1 := by rw [famBlocks_N, ← haJ, hadeg]
  obtain ⟨hYi, -⟩ := listProduct_irr_unit F T hA lF hN
  have hYf := SmoothRep.hasFiniteLength_of_isIrreducible hYi
  have hclsY : cls F T (listProduct F T lF hN) hYf = cls F T π hπf := by
    rw [cls_listProduct, famBlocks_cl, hπcls]
  obtain ⟨e⟩ := nonempty_iso_of_cls_eq F T hirr hYi hπf hYf hclsY.symm
  refine ⟨listShape F T lF hN, fun i => lF[i.1].rep, fun i => ?_, ⟨e⟩⟩
  exact famBlocks_isTadicXBlock F T hA hC hD J hJU hb _ (List.getElem_mem _)

/-- **Tadić's Lemma 4.8(ii) from its inputs.** -/
theorem tadicBlockReductionFromInputs : TadicBlockReductionFromInputs.{uF, uV} F T := by
  intro hin
  refine (tadicBlockReduction_iff F T).mpr fun m => ?_
  induction m using Nat.strong_induction_on with
  | _ m ih => exact step F T hin m ih

end Langlands.Classification.TadicBlockReductionAssembly
