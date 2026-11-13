import Langlands.Representation.Classification.TadicBlockRing
import Langlands.Representation.Classification.TadicBlockCombinatorics
import Langlands.Representation.Classification.TadicBlockSteinberg
import Langlands.Representation.Classification.MultisegmentConstituentRealTwistCompatibilityProof
import Langlands.Representation.Classification.TwoSupercuspidalAdjacentReducibilityProof
import Langlands.Representation.Classification.TadicComplementarySeriesOpenIntervalStatement

/-!
# Classes of rectangles and unitary blocks

Classes in `R` of the Zelevinsky socles of the rectangles `a(n,d)^(ν^α ρ)`, the
multiset form of the product rule of `TadicBlockRing`, and the irreducibility, unitarity
and class of the complementary products `ν^α σ × ν^(-α) σ`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace Langlands.Classification.TadicBlockBlocks

open Aubert Aubert.SegmentPolynomialSurjectivity PadicField.TopologicalData GeneralLinear
open TadicBlockRing TadicBlockCombinatorics

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

attribute [local instance] ringR

/-! ### Classes of socles -/

theorem degree_eq_of_isZelevinskySocle {N : ℕ} {e : T.Multisegment.{max uF uV, uF}}
    {X : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear N F.Carrier)}
    (h : e.IsZelevinskySocle X) : e.degree = N := by
  obtain ⟨d, rfl, -⟩ := h
  exact degree_multisegment F T d

/-- Zelevinsky socles of one multisegment have the same class, in whatever rank they are
presented. -/
theorem cls_eq_of_isZelevinskySocle {e : T.Multisegment.{max uF uV, uF}} {N N' : ℕ}
    {X : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear N F.Carrier)}
    {Y : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear N' F.Carrier)}
    (hX : e.IsZelevinskySocle X) (hY : e.IsZelevinskySocle Y)
    (hXf : letI := T.topology; X.HasFiniteLength) (hYf : letI := T.topology; Y.HasFiniteLength) :
    cls F T X hXf = cls F T Y hYf := by
  let := T.topology
  have h1 := degree_eq_of_isZelevinskySocle F T hX
  have h2 := degree_eq_of_isZelevinskySocle F T hY
  subst h1
  subst h2
  obtain ⟨e'⟩ := nonempty_iso_of_isZelevinskySocle hX hY
  exact cls_eq_of_iso F T e' hXf hYf

theorem cls_cast {N N' : ℕ} (h : N = N')
    (X : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear N F.Carrier))
    (hX : letI := T.topology; X.HasFiniteLength)
    (hX' : letI := T.topology; (h ▸ X).HasFiniteLength) :
    cls F T (h ▸ X) hX' = cls F T X hX := by
  subst h
  rfl

/-- A chosen Zelevinsky socle of the rectangle of `q`. -/
def rectSocle (q : RParam.{uF, max uF uV} T) :
    letI := T.topology
    SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear q.rect.degree F.Carrier) :=
  letI := T.topology
  Classical.choose (exists_isZelevinskySocle F T q.rect)

theorem rectSocle_spec (q : RParam.{uF, max uF uV} T) :
    q.rect.IsZelevinskySocle (rectSocle F T q) :=
  letI := T.topology
  Classical.choose_spec (exists_isZelevinskySocle F T q.rect)

/-- The class `[⟨a(n,d)^(ν^α ρ)⟩]` in `R`. -/
def rectCls (q : RParam.{uF, max uF uV} T) : GradedGrothendieckGroup.{uF, uV} F T :=
  letI := T.topology
  cls F T (rectSocle F T q)
    (SmoothRep.hasFiniteLength_of_isIrreducible
      (isIrreducible_of_isZelevinskySocle F T (rectSocle_spec F T q)))

theorem cls_eq_rectCls {q : RParam.{uF, max uF uV} T} {N : ℕ}
    {X : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear N F.Carrier)}
    (hX : q.rect.IsZelevinskySocle X) (hXf : letI := T.topology; X.HasFiniteLength) :
    cls F T X hXf = rectCls F T q :=
  cls_eq_of_isZelevinskySocle F T hX (rectSocle_spec F T q) _ _

theorem rectCls_eq_basisClass (q : RParam.{uF, max uF uV} T) :
    letI := T.topology
    IsLabel F T q.rect q.rect.degree (GeneralLinear.irreducibleIsoClass _ F.Carrier
        (rectSocle F T q) (isIrreducible_of_isZelevinskySocle F T (rectSocle_spec F T q))) ∧
      rectCls F T q = basisClass F T q.rect.degree (GeneralLinear.irreducibleIsoClass _ F.Carrier
        (rectSocle F T q) (isIrreducible_of_isZelevinskySocle F T (rectSocle_spec F T q))) :=
  ⟨isLabel_of_isZelevinskySocle F T (rectSocle_spec F T q),
    cls_eq_basisClass F T _ _⟩

theorem isEffective_rectCls (q : RParam.{uF, max uF uV} T) : IsEffective F T (rectCls F T q) := by
  rw [(rectCls_eq_basisClass F T q).2]
  exact isEffective_basisClass F T _ _

theorem isEffective_prod_rectCls (J : Multiset (RParam.{uF, max uF uV} T)) :
    IsEffective F T ((J.map (rectCls F T)).prod) := by
  induction J using Multiset.induction_on with
  | empty =>
    rw [Multiset.map_zero, Multiset.prod_zero]
    obtain ⟨c0, hc0⟩ := gradedUnit_eq_basisClass.{uF, uV} F T
    change IsEffective F T (gradedUnit F T)
    rw [hc0]
    exact isEffective_basisClass F T 0 c0
  | cons q J ih =>
    rw [Multiset.map_cons, Multiset.prod_cons]
    exact isEffective_mul F T (isEffective_rectCls F T q) ih

/-- **Zelevinsky 8.4 for rectangles**: the label of `∑ rect` occurs in `∏ [⟨rect⟩]`. -/
theorem one_le_coeff_prod_rectCls (J : Multiset (RParam.{uF, max uF uV} T)) {M : ℕ}
    {L : Label.{uF, uV} F T M} (hL : IsLabel F T (J.map RParam.rect).sum M L) :
    1 ≤ coeff F T M L ((J.map (rectCls F T)).prod) := by
  induction J using Multiset.induction_on generalizing M with
  | empty =>
    rw [Multiset.map_zero, Multiset.sum_zero] at hL
    rw [Multiset.map_zero, Multiset.prod_zero]
    have h0 := one_le_coeff_zetaR_of_isLabel F T hL
    rwa [zetaR_zero] at h0
  | cons q J ih =>
    rw [Multiset.map_cons, Multiset.sum_cons] at hL
    rw [Multiset.map_cons, Multiset.prod_cons]
    obtain ⟨Ls, hLs⟩ := exists_isLabel_of F T (J.map RParam.rect).sum
    have hih := ih hLs
    have hE : IsEffective F T ((J.map (rectCls F T)).prod - basisClass F T _ Ls) :=
      isEffective_sub_basisClass F T (isEffective_prod_rectCls F T J) hih
    obtain ⟨hlq, heq⟩ := rectCls_eq_basisClass F T q
    have e : rectCls F T q * (J.map (rectCls F T)).prod =
        rectCls F T q * basisClass F T _ Ls +
          rectCls F T q * ((J.map (rectCls F T)).prod - basisClass F T _ Ls) := by ring
    rw [e, map_add]
    have h1 := one_le_coeff_basisClass_mul F T hlq hLs hL
    rw [← heq] at h1
    have h2 := isEffective_mul F T (isEffective_rectCls F T q) hE M L
    omega

/-- **Products of rectangle socles.** An irreducible representation whose class is
`∏ [⟨rect q⟩]` is a Zelevinsky socle of `∑ rect q`. -/
theorem isZelevinskySocle_of_cls_eq_prod_rectCls {N : ℕ}
    {π : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear N F.Carrier)}
    (hπ : letI := T.topology; π.IsIrreducible) (hfl : letI := T.topology; π.HasFiniteLength)
    (J : Multiset (RParam.{uF, max uF uV} T)) (h : cls F T π hfl = (J.map (rectCls F T)).prod) :
    (J.map RParam.rect).sum.IsZelevinskySocle π := by
  let := T.topology
  obtain ⟨τ, hτ⟩ := exists_isZelevinskySocle F T (J.map RParam.rect).sum
  have hL := isLabel_of_isZelevinskySocle F T hτ
  have h1 := one_le_coeff_prod_rectCls F T J hL
  rw [← h, cls_eq_basisClass F T hπ] at h1
  by_cases hN : (J.map RParam.rect).sum.degree = N
  · subst hN
    by_cases hc' : GeneralLinear.irreducibleIsoClass _ F.Carrier π hπ =
        GeneralLinear.irreducibleIsoClass _ F.Carrier τ (isIrreducible_of_isZelevinskySocle F T hτ)
    · obtain ⟨e⟩ := (SmoothRep.irreducibleIsoClass_eq_iff hπ _).mp hc'
      exact Multisegment.IsZelevinskySocle.of_iso hτ e.symm
    · rw [coeff_basisClass_of_ne F T _ hc'] at h1
      omega
  · rw [basisClass, coeff_gradedInclusion_of_ne F T hN] at h1
    omega


/-! ### Twists and linkage of rectangles -/

theorem tadicMultisegment_twist (ρ : T.CuspidalDatum.{max uF uV, uF}) (n d : ℕ) (hd : 0 < d)
    (β : ℝ) : (tadicMultisegment ρ n d hd).twist β = tadicMultisegment (ρ.twist β) n d hd := by
  unfold tadicMultisegment Multisegment.twist
  rw [Multiset.map_map]
  refine Multiset.map_congr rfl fun j _ => ?_
  simp only [Function.comp, tadicCenteredSegment, Segment.twist, CuspidalDatum.twist_twist]
  congr 2
  ring

theorem RParam.rect_mk (ρ : T.CuspidalDatum.{max uF uV, uF}) (n d : ℕ) (hd : 0 < d) (α : ℝ) :
    (⟨ρ, n, d, hd, α⟩ : RParam.{uF, max uF uV} T).rect = tadicMultisegment (ρ.twist α) n d hd :=
  rfl

theorem RParam.rect_eq_twist (q : RParam.{uF, max uF uV} T) :
    q.rect = (tadicMultisegment q.ρ q.n q.d q.hd).twist q.α :=
  (tadicMultisegment_twist F T q.ρ q.n q.d q.hd q.α).symm

theorem twist_eq_twist_iff (ρ : T.CuspidalDatum.{max uF uV, uF}) {s t : ℝ} :
    ρ.twist s = ρ.twist t ↔ s = t :=
  ⟨cuspidalDatum_twist_injective ρ, fun h => h ▸ rfl⟩

/-- Segments of `ν^β a(n,d)^ρ` and `ν^(-β) a(n,d)^ρ` are never linked for `0 < |β| < 1/2`:
they lie in different `ν^ℤ`-orbits. -/
theorem not_isLinked_twist_pair (ρ : T.CuspidalDatum.{max uF uV, uF}) {n d : ℕ} (hd : 0 < d)
    {β : ℝ} (hβ0 : β ≠ 0) (hβ : |β| < 1 / 2) {Δ Δ' : T.Segment.{max uF uV, uF}}
    (hΔ : Δ ∈ tadicMultisegment (ρ.twist β) n d hd)
    (hΔ' : Δ' ∈ tadicMultisegment (ρ.twist (-β)) n d hd) : ¬ Δ.IsLinked Δ' := by
  obtain ⟨j, -, rfl⟩ := mem_tadicMultisegment.mp hΔ
  obtain ⟨j', -, rfl⟩ := mem_tadicMultisegment.mp hΔ'
  rintro ⟨-, -, Γ, hΓ⟩
  have h1 : (tadicCenteredSegment (ρ.twist β) d hd ((j : ℝ) - ((n : ℝ) - 1) / 2)).base ∈
      Γ.support := by rw [hΓ]; exact Or.inl (Segment.base_mem_support _)
  have h2 : (tadicCenteredSegment (ρ.twist (-β)) d hd ((j' : ℝ) - ((n : ℝ) - 1) / 2)).base ∈
      Γ.support := by rw [hΓ]; exact Or.inr (Segment.base_mem_support _)
  obtain ⟨i, -, hi⟩ := h1
  obtain ⟨i', -, hi'⟩ := h2
  simp only [Segment.member, tadicCenteredSegment, CuspidalDatum.twist_twist] at hi hi'
  have e : (ρ.twist ((j : ℝ) - ((n : ℝ) - 1) / 2 - ((d : ℝ) - 1) / 2 + β)).twist
      ((i' : ℝ) - i) = ρ.twist ((j' : ℝ) - ((n : ℝ) - 1) / 2 - ((d : ℝ) - 1) / 2 + -β) := by
    rw [← hi, ← hi', CuspidalDatum.twist_twist]
    congr 1
    ring
  rw [CuspidalDatum.twist_twist] at e
  have e' := (twist_eq_twist_iff F T ρ).mp e
  have hk : (2 * β : ℝ) = (((j' : ℤ) - j - i' + i : ℤ) : ℝ) := by push_cast; linarith
  have hlt : |(((j' : ℤ) - j - i' + i : ℤ) : ℝ)| < 1 := by
    rw [← hk, abs_mul, abs_two]; linarith
  have hz : (j' : ℤ) - j - i' + i = 0 := by
    have : |((j' : ℤ) - j - i' + i)| < 1 := by exact_mod_cast hlt
    rw [abs_lt] at this
    omega
  rw [hz] at hk
  push_cast at hk
  exact hβ0 (by linarith)


/-! ### Complementary products -/

section Complementary

variable {M : ℕ} (hM : 0 < M)

/-- The exponents `(β, -β)` of the complementary product. -/
abbrev cExp (β : ℝ) : Fin (BlockShape.uniform 2 M hM).length → ℝ :=
  fun i => if (i : ℕ) = 0 then β else -β

theorem twistedBlocks_isIrreducible
    (σ : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear M F.Carrier))
    (hσ : letI := T.topology; σ.IsIrreducible) (u : Fin (BlockShape.uniform 2 M hM).length → ℝ) :
    letI := T.topology
    ∀ i, (T.twistedBlocks (BlockShape.uniform 2 M hM) (fun _ => σ) u i).IsIrreducible := by
  let := T.topology
  intro i
  exact (SmoothRep.isIrreducible_twist_iff _ (T.isOpen_ker_determinantPowerCharacter _ _) σ).mpr hσ

/-- The class of `ν^β σ × ν^(-β) σ` is `[ν^β σ] [ν^(-β) σ]`. -/
theorem cls_tadicComplementaryProduct
    (σ : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear M F.Carrier))
    (hσ : letI := T.topology; σ.IsIrreducible) (β : ℝ)
    (hfl : letI := T.topology; (tadicComplementaryProduct hM σ β).HasFiniteLength) :
    letI := T.topology
    cls F T (tadicComplementaryProduct hM σ β) hfl =
      cls F T (T.segmentFactor σ β) (SmoothRep.hasFiniteLength_of_isIrreducible
          ((SmoothRep.isIrreducible_twist_iff _ _ σ).mpr hσ)) *
        cls F T (T.segmentFactor σ (-β)) (SmoothRep.hasFiniteLength_of_isIrreducible
          ((SmoothRep.isIrreducible_twist_iff _ _ σ).mpr hσ)) := by
  let := T.topology
  have h := cls_product F T (BlockShape.uniform 2 M hM)
    (T.twistedBlocks (BlockShape.uniform 2 M hM) (fun _ => σ) (cExp hM β))
    (twistedBlocks_isIrreducible F T hM σ hσ _)
  have h2 := Fin.prod_univ_two (fun i : Fin 2 => cls F T
    (T.twistedBlocks (BlockShape.uniform 2 M hM) (fun _ => σ) (cExp hM β) i)
    (SmoothRep.hasFiniteLength_of_isIrreducible (twistedBlocks_isIrreducible F T hM σ hσ _ i)))
  exact h.trans h2

include hM in
theorem segmentFactor_isZelevinskySocle {ρ : T.CuspidalDatum.{max uF uV, uF}} {n d : ℕ}
    {hd : 0 < d}
    {σ : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear M F.Carrier)}
    (hσ : (tadicMultisegment ρ n d hd).IsZelevinskySocle σ) (β : ℝ) :
    (tadicMultisegment (ρ.twist β) n d hd).IsZelevinskySocle (T.segmentFactor σ β) := by
  let := T.topology
  rw [← tadicMultisegment_twist]
  exact ((multisegmentConstituentRealTwistCompatibility.{uF, max uF uV} F T M hM
    (tadicMultisegment ρ n d hd) β σ).1).mp hσ

include hM in
theorem cls_segmentFactor_eq_rectCls {ρ : T.CuspidalDatum.{max uF uV, uF}} {n d : ℕ}
    {hd : 0 < d}
    {σ : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear M F.Carrier)}
    (hσ : (tadicMultisegment ρ n d hd).IsZelevinskySocle σ) (β : ℝ)
    (hfl : letI := T.topology; (T.segmentFactor σ β).HasFiniteLength) :
    cls F T (T.segmentFactor σ β) hfl = rectCls F T ⟨ρ, n, d, hd, β⟩ := by
  have h := segmentFactor_isZelevinskySocle F T hM hσ β
  rw [← RParam.rect_mk] at h
  exact cls_eq_rectCls F T h hfl

/-- `ν^β σ × ν^(-β) σ` is irreducible for `|β| < 1/2` and a unitarizable socle `σ` of
`a(n,d)^ρ`: Bernstein's 2.5(i) for `β = 0`, Zelevinsky's 8.5 otherwise. -/
theorem tadicComplementaryProduct_isIrreducible
    (hA : BernsteinUnitaryProductIrreducibility.{uF, uV} F T)
    (hD : UnlinkedSocleProductIrreducibility.{uF, uV} F T)
    {ρ : T.CuspidalDatum.{max uF uV, uF}} {n d : ℕ} {hd : 0 < d}
    {σ : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear M F.Carrier)}
    (hσ : (tadicMultisegment ρ n d hd).IsZelevinskySocle σ)
    (hσu : letI := T.topology; IsUnitarizable σ.representation) {β : ℝ} (hβ : |β| < 1 / 2) :
    letI := T.topology
    (tadicComplementaryProduct hM σ β).IsIrreducible := by
  let := T.topology
  have hσi := isIrreducible_of_isZelevinskySocle F T hσ
  by_cases hβ0 : β = 0
  · subst hβ0
    refine (hA (2 * M) (BlockShape.uniform 2 M hM)
      (T.twistedBlocks (BlockShape.uniform 2 M hM) (fun _ => σ) (cExp hM 0)) fun i => ?_).1
    refine ⟨twistedBlocks_isIrreducible F T hM σ hσi _ i, ?_⟩
    have hu : cExp hM 0 i = 0 := by simp [cExp]
    change IsUnitarizable (T.segmentFactor σ (cExp hM 0 i)).representation
    rw [hu]
    exact (isUnitarizable_iff_of_equiv
      (SmoothRep.equivOfIso (segmentFactorZeroIso F T σ))).mpr hσu
  · have hsoc := hD (2 * M) (BlockShape.uniform 2 M hM)
      (fun i => tadicMultisegment (ρ.twist (cExp hM β i)) n d hd)
      (T.twistedBlocks (BlockShape.uniform 2 M hM) (fun _ => σ) (cExp hM β))
      (fun i => segmentFactor_isZelevinskySocle F T hM hσ _) ?_
    · exact isIrreducible_of_isZelevinskySocle F T hsoc
    · intro i j hij Δ hΔ Δ' hΔ'
      fin_cases i <;> fin_cases j
      · exact absurd rfl hij
      · simp only [cExp] at hΔ hΔ'
        simp at hΔ hΔ'
        exact not_isLinked_twist_pair F T ρ hd hβ0 hβ hΔ hΔ'
      · simp only [cExp] at hΔ hΔ'
        simp at hΔ hΔ'
        have hΔ'' : Δ' ∈ tadicMultisegment (ρ.twist (-(-β))) n d hd := by rwa [neg_neg]
        exact not_isLinked_twist_pair F T ρ hd (neg_ne_zero.mpr hβ0)
          (by rw [abs_neg]; exact hβ) hΔ hΔ''
      · exact absurd rfl hij

/-- `ν^β σ × ν^(-β) σ` is unitarizable for `|β| < 1/2` (the open-interval clause of Tadić's
Proposition 2.9). -/
theorem tadicComplementaryProduct_isUnitarizable
    (hA : BernsteinUnitaryProductIrreducibility.{uF, uV} F T)
    (hC : ComplementarySeriesOpenIntervalUnitarity.{uF, uV} F T)
    (hD : UnlinkedSocleProductIrreducibility.{uF, uV} F T)
    {ρ : T.CuspidalDatum.{max uF uV, uF}} {n d : ℕ} {hd : 0 < d}
    {σ : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear M F.Carrier)}
    (hσ : (tadicMultisegment ρ n d hd).IsZelevinskySocle σ)
    (hσu : letI := T.topology; IsUnitarizable σ.representation) {β : ℝ} (hβ : |β| < 1 / 2) :
    letI := T.topology
    IsUnitarizable (tadicComplementaryProduct hM σ β).representation := by
  let := T.topology
  have hσi := isIrreducible_of_isZelevinskySocle F T hσ
  exact hC M hM σ (1 / 2) hσi hσu (by norm_num) (fun α hα =>
    tadicComplementaryProduct_isIrreducible F T hM hA hD hσ hσu
      (by rw [abs_lt]; exact ⟨hα.1, hα.2⟩)) β (by rw [abs_lt] at hβ; exact ⟨hβ.1, hβ.2⟩)

end Complementary


/-! ### Irreducible unitarizable blocks and their products -/

/-- An irreducible unitarizable representation of `GL_N`, `N > 0`. -/
structure UIrr where
  N : ℕ
  pos : 0 < N
  rep : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear N F.Carrier)
  irr : letI := T.topology; rep.IsIrreducible
  unit : letI := T.topology; IsUnitarizable rep.representation

namespace UIrr

variable {F T}

/-- The class of a block. -/
def cl (b : UIrr.{uF, uV} F T) : GradedGrothendieckGroup.{uF, uV} F T :=
  letI := T.topology
  cls F T b.rep (SmoothRep.hasFiniteLength_of_isIrreducible b.irr)

end UIrr

/-- The block shape of a list of blocks, of total rank `n`. -/
def listShape (l : List (UIrr.{uF, uV} F T)) {n : ℕ} (h : (l.map UIrr.N).sum = n) : BlockShape n where
  length := l.length
  size i := l[i.1].N
  positive i := l[i.1].pos
  sum_eq := by rw [Fin.sum_univ_fun_getElem]; exact h

/-- The normalized product of a list of blocks. -/
def listProduct (l : List (UIrr.{uF, uV} F T)) {n : ℕ} (h : (l.map UIrr.N).sum = n) :
    letI := T.topology
    SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier) :=
  letI := T.topology
  (T.normalizedProductInductionFunctor (listShape F T l h)).obj fun i => l[i.1].rep

theorem listProduct_irr_unit (hA : BernsteinUnitaryProductIrreducibility.{uF, uV} F T)
    (l : List (UIrr.{uF, uV} F T)) {n : ℕ} (h : (l.map UIrr.N).sum = n) :
    letI := T.topology
    (listProduct F T l h).IsIrreducible ∧ IsUnitarizable (listProduct F T l h).representation := by
  let := T.topology
  exact hA n (listShape F T l h) (fun i => l[i.1].rep) fun i => ⟨l[i.1].irr, l[i.1].unit⟩

theorem cls_listProduct (l : List (UIrr.{uF, uV} F T)) {n : ℕ} (h : (l.map UIrr.N).sum = n)
    (hfl : letI := T.topology; (listProduct F T l h).HasFiniteLength) :
    cls F T (listProduct F T l h) hfl = (l.map UIrr.cl).prod := by
  let := T.topology
  exact (cls_product F T (listShape F T l h) (fun i => l[i.1].rep) fun i => l[i.1].irr).trans
    (Fin.prod_univ_fun_getElem l UIrr.cl)

/-! ### Blocks from rectangle parameters -/

/-- The unitarity hypothesis on the socles of `a(n,d)^ρ` for the parameters of `q`. -/
def BaseUnitary (q : RParam.{uF, max uF uV} T) : Prop :=
  ∀ {N : ℕ} (X : letI := T.topology;
    SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear N F.Carrier)),
    (tadicMultisegment q.ρ q.n q.d q.hd).IsZelevinskySocle X →
      letI := T.topology; IsUnitarizable X.representation

/-- `⟨a(n,d)^ρ⟩` for admissible parameters with `α = 0` and a unitarizable socle. -/
def zeroBlk (q : RParam.{uF, max uF uV} T) (hv : q.Valid) (hα : q.α = 0)
    (hu : BaseUnitary F T q) : UIrr.{uF, uV} F T where
  N := q.rect.degree
  pos := by
    rw [RParam.rect, tadicMultisegment_degree]
    exact Nat.mul_pos hv.2.1 (Nat.mul_pos q.hd (q.ρ.twist q.α).rank_pos)
  rep := rectSocle F T q
  irr := isIrreducible_of_isZelevinskySocle F T (rectSocle_spec F T q)
  unit := by
    have h := rectSocle_spec F T q
    change (tadicMultisegment (q.ρ.twist q.α) q.n q.d q.hd).IsZelevinskySocle _ at h
    rw [hα, CuspidalDatum.twist_zero] at h
    exact hu _ h

theorem zeroBlk_cl (q : RParam.{uF, max uF uV} T) (hv : q.Valid) (hα : q.α = 0)
    (hu : BaseUnitary F T q) : (zeroBlk F T q hv hα hu).cl = rectCls F T q := rfl

/-- A chosen Zelevinsky socle of `a(n,d)^ρ` for the parameters of `q`. -/
def baseSocle (q : RParam.{uF, max uF uV} T) :
    letI := T.topology
    SmoothRep.{0, uF, max uF uV} ℂ
      (GeneralLinear (tadicMultisegment q.ρ q.n q.d q.hd).degree F.Carrier) :=
  letI := T.topology
  Classical.choose (exists_isZelevinskySocle F T (tadicMultisegment q.ρ q.n q.d q.hd))

theorem baseSocle_spec (q : RParam.{uF, max uF uV} T) :
    (tadicMultisegment q.ρ q.n q.d q.hd).IsZelevinskySocle (baseSocle F T q) :=
  letI := T.topology
  Classical.choose_spec (exists_isZelevinskySocle F T (tadicMultisegment q.ρ q.n q.d q.hd))

theorem baseDegree_pos (q : RParam.{uF, max uF uV} T) (hv : q.Valid) :
    0 < (tadicMultisegment q.ρ q.n q.d q.hd).degree := by
  rw [tadicMultisegment_degree]
  exact Nat.mul_pos hv.2.1 (Nat.mul_pos q.hd q.ρ.rank_pos)

/-- The complementary product `ν^α σ × ν^(-α) σ`, `σ = ⟨a(n,d)^ρ⟩`. -/
def pairRep (q : RParam.{uF, max uF uV} T) (hv : q.Valid) :
    letI := T.topology
    SmoothRep.{0, uF, max uF uV} ℂ
      (GeneralLinear (2 * (tadicMultisegment q.ρ q.n q.d q.hd).degree) F.Carrier) :=
  tadicComplementaryProduct (baseDegree_pos F T q hv) (baseSocle F T q) q.α

theorem pairRep_irr (hA : BernsteinUnitaryProductIrreducibility.{uF, uV} F T)
    (hD : UnlinkedSocleProductIrreducibility.{uF, uV} F T)
    (q : RParam.{uF, max uF uV} T) (hv : q.Valid) (hu : BaseUnitary F T q) :
    letI := T.topology
    (pairRep F T q hv).IsIrreducible := by
  let := T.topology
  have hσ := baseSocle_spec F T q
  have hM := baseDegree_pos F T q hv
  have hu' : IsUnitarizable (baseSocle F T q).representation := hu _ hσ
  have hα : |q.α| < 1 / 2 := hv.2.2
  have key := tadicComplementaryProduct_isIrreducible F T hM hA hD hσ hu' hα
  exact key

theorem pairRep_unit (hA : BernsteinUnitaryProductIrreducibility.{uF, uV} F T)
    (hC : ComplementarySeriesOpenIntervalUnitarity.{uF, uV} F T)
    (hD : UnlinkedSocleProductIrreducibility.{uF, uV} F T)
    (q : RParam.{uF, max uF uV} T) (hv : q.Valid) (hu : BaseUnitary F T q) :
    letI := T.topology
    IsUnitarizable (pairRep F T q hv).representation := by
  let := T.topology
  have hσ := baseSocle_spec F T q
  exact tadicComplementaryProduct_isUnitarizable F T (baseDegree_pos F T q hv) hA hC hD hσ
    (hu _ hσ) hv.2.2

/-- The complementary block `ν^α σ × ν^(-α) σ`, `σ = ⟨a(n,d)^ρ⟩`. -/
def pairBlk (hA : BernsteinUnitaryProductIrreducibility.{uF, uV} F T)
    (hC : ComplementarySeriesOpenIntervalUnitarity.{uF, uV} F T)
    (hD : UnlinkedSocleProductIrreducibility.{uF, uV} F T)
    (q : RParam.{uF, max uF uV} T) (hv : q.Valid) (hu : BaseUnitary F T q) :
    UIrr.{uF, uV} F T where
  N := 2 * (tadicMultisegment q.ρ q.n q.d q.hd).degree
  pos := Nat.mul_pos two_pos (baseDegree_pos F T q hv)
  rep := pairRep F T q hv
  irr := pairRep_irr F T hA hD q hv hu
  unit := pairRep_unit F T hA hC hD q hv hu

theorem pairBlk_cl (hA hC hD) (q : RParam.{uF, max uF uV} T) (hv : q.Valid) (hu) :
    (pairBlk F T hA hC hD q hv hu).cl = rectCls F T q * rectCls F T q.refl := by
  let := T.topology
  have hσ := baseSocle_spec F T q
  have hM := baseDegree_pos F T q hv
  have hσi := isIrreducible_of_isZelevinskySocle F T hσ
  change cls F T (tadicComplementaryProduct hM (baseSocle F T q) q.α) _ = _
  rw [cls_tadicComplementaryProduct F T hM _ hσi, cls_segmentFactor_eq_rectCls F T hM hσ,
    cls_segmentFactor_eq_rectCls F T hM hσ]
  rfl


/-! ### Blocks of a reflection-invariant family -/

/-- Admissible, reflection-invariant parameter families with unitarizable base socles. -/
structure UFamily (J : Multiset (RParam.{uF, max uF uV} T)) : Prop where
  valid : ∀ q ∈ J, q.Valid
  refl : J.map RParam.refl = J
  unit : ∀ q ∈ J, BaseUnitary F T q

theorem UFamily.add {J J' : Multiset (RParam.{uF, max uF uV} T)} (h : UFamily F T J)
    (h' : UFamily F T J') : UFamily F T (J + J') :=
  ⟨fun q hq => (Multiset.mem_add.mp hq).elim (h.valid q) (h'.valid q),
    by rw [Multiset.map_add, h.refl, h'.refl],
    fun q hq => by
      rcases Multiset.mem_add.mp hq with h1 | h1
      exacts [h.unit q h1, h'.unit q h1]⟩

/-- The parameters with `α = 0`. -/
abbrev zeroPart (J : Multiset (RParam.{uF, max uF uV} T)) : Multiset (RParam.{uF, max uF uV} T) :=
  J.filter fun q => q.α = 0

/-- The parameters with `α > 0`. -/
abbrev posPart (J : Multiset (RParam.{uF, max uF uV} T)) : Multiset (RParam.{uF, max uF uV} T) :=
  J.filter fun q => 0 < q.α

theorem split_family {J : Multiset (RParam.{uF, max uF uV} T)} (h : J.map RParam.refl = J) :
    J = zeroPart F T J + posPart F T J + (posPart F T J).map RParam.refl := by
  classical
  have hneg : (posPart F T J).map RParam.refl = J.filter fun q => q.α < 0 := by
    conv_rhs => rw [← h]
    rw [Multiset.filter_map]
    congr 1
    refine Multiset.filter_congr fun q _ => ?_
    simp [RParam.refl]
  rw [hneg, add_assoc]
  have h1 := Multiset.filter_add_not (fun q : RParam.{uF, max uF uV} T => q.α = 0) J
  have h2 := Multiset.filter_add_not (fun q : RParam.{uF, max uF uV} T => 0 < q.α)
    (J.filter fun q => ¬ q.α = 0)
  rw [Multiset.filter_filter, Multiset.filter_filter] at h2
  have e1 : (J.filter fun q => 0 < q.α ∧ ¬ q.α = 0) = posPart F T J :=
    Multiset.filter_congr fun q _ => ⟨fun h => h.1, fun h => ⟨h, ne_of_gt h⟩⟩
  have e2 : (J.filter fun q => ¬ 0 < q.α ∧ ¬ q.α = 0) = J.filter fun q => q.α < 0 :=
    Multiset.filter_congr fun q _ => ⟨fun h => lt_of_le_of_ne (not_lt.mp h.1) h.2,
      fun h => ⟨not_lt.mpr h.le, ne_of_lt h⟩⟩
  rw [e1, e2] at h2
  rw [h2]
  exact h1.symm

theorem prod_map_toList {β : Type*} [CommMonoid β] {α : Type*} (s : Multiset α) (f : α → β) :
    (s.toList.map f).prod = (s.map f).prod := by
  rw [← Multiset.prod_coe, ← Multiset.map_coe, Multiset.coe_toList]

theorem sum_map_toList {α : Type*} (s : Multiset α) (f : α → ℕ) :
    (s.toList.map f).sum = (s.map f).sum := by
  rw [← Multiset.sum_coe, ← Multiset.map_coe, Multiset.coe_toList]

variable (hA : BernsteinUnitaryProductIrreducibility.{uF, uV} F T)
  (hC : ComplementarySeriesOpenIntervalUnitarity.{uF, uV} F T)
  (hD : UnlinkedSocleProductIrreducibility.{uF, uV} F T)

/-- The blocks of a family: `⟨a(n,d)^ρ⟩` for `α = 0` and the complementary products for the
pairs `±α`, `α > 0`. -/
def famBlocks (J : Multiset (RParam.{uF, max uF uV} T)) (hJ : UFamily F T J) :
    List (UIrr.{uF, uV} F T) :=
  ((zeroPart F T J).attach.toList.map fun q =>
      zeroBlk F T q.1 (hJ.valid _ (Multiset.mem_of_mem_filter q.2))
        (Multiset.of_mem_filter (p := fun r : RParam.{uF, max uF uV} T => r.α = 0) q.2)
        (hJ.unit _ (Multiset.mem_of_mem_filter q.2))) ++
    ((posPart F T J).attach.toList.map fun q =>
      pairBlk F T hA hC hD q.1 (hJ.valid _ (Multiset.mem_of_mem_filter q.2))
        (hJ.unit _ (Multiset.mem_of_mem_filter q.2)))

theorem famBlocks_cl (J : Multiset (RParam.{uF, max uF uV} T)) (hJ : UFamily F T J) :
    ((famBlocks F T hA hC hD J hJ).map UIrr.cl).prod = (J.map (rectCls F T)).prod := by
  rw [famBlocks, List.map_append, List.prod_append, List.map_map, List.map_map,
    prod_map_toList, prod_map_toList]
  have e1 : ((zeroPart F T J).attach.map (UIrr.cl ∘ fun q =>
      zeroBlk F T q.1 (hJ.valid _ (Multiset.mem_of_mem_filter q.2))
        (Multiset.of_mem_filter (p := fun r : RParam.{uF, max uF uV} T => r.α = 0) q.2)
        (hJ.unit _ (Multiset.mem_of_mem_filter q.2)))) =
      (zeroPart F T J).attach.map fun q => rectCls F T q.1 :=
    Multiset.map_congr rfl fun q _ => zeroBlk_cl F T _ _ _ _
  have e2 : ((posPart F T J).attach.map (UIrr.cl ∘ fun q =>
      pairBlk F T hA hC hD q.1 (hJ.valid _ (Multiset.mem_of_mem_filter q.2))
        (hJ.unit _ (Multiset.mem_of_mem_filter q.2)))) =
      (posPart F T J).attach.map fun q => rectCls F T q.1 * rectCls F T q.1.refl :=
    Multiset.map_congr rfl fun q _ => pairBlk_cl F T hA hC hD _ _ _
  rw [e1, e2, Multiset.attach_map_val' _ (rectCls F T),
    Multiset.attach_map_val' _ fun q => rectCls F T q * rectCls F T q.refl,
    Multiset.prod_map_mul]
  conv_rhs => rw [split_family F T hJ.refl]
  rw [Multiset.map_add, Multiset.map_add, Multiset.prod_add, Multiset.prod_add,
    Multiset.map_map, mul_assoc]
  rfl

theorem degree_rect (q : RParam.{uF, max uF uV} T) :
    q.rect.degree = (tadicMultisegment q.ρ q.n q.d q.hd).degree := by
  rw [RParam.rect, tadicMultisegment_degree, tadicMultisegment_degree]
  rfl

theorem degree_sum_rect (J : Multiset (RParam.{uF, max uF uV} T)) :
    (J.map RParam.rect).sum.degree = (J.map fun q => q.rect.degree).sum := by
  induction J using Multiset.induction_on with
  | empty => simp [Multisegment.degree]
  | cons q J ih =>
    rw [Multiset.map_cons, Multiset.sum_cons, Multiset.map_cons, Multiset.sum_cons, ← ih]
    simp [Multisegment.degree, Multiset.map_add, Multiset.sum_add]

theorem famBlocks_N (J : Multiset (RParam.{uF, max uF uV} T)) (hJ : UFamily F T J) :
    ((famBlocks F T hA hC hD J hJ).map UIrr.N).sum = (J.map RParam.rect).sum.degree := by
  rw [famBlocks, List.map_append, List.sum_append, List.map_map, List.map_map,
    sum_map_toList, sum_map_toList, degree_sum_rect]
  have e1 : ((zeroPart F T J).attach.map (UIrr.N ∘ fun q =>
      zeroBlk F T q.1 (hJ.valid _ (Multiset.mem_of_mem_filter q.2))
        (Multiset.of_mem_filter (p := fun r : RParam.{uF, max uF uV} T => r.α = 0) q.2)
        (hJ.unit _ (Multiset.mem_of_mem_filter q.2)))) =
      (zeroPart F T J).attach.map fun q => q.1.rect.degree :=
    Multiset.map_congr rfl fun q _ => rfl
  have e2 : ((posPart F T J).attach.map (UIrr.N ∘ fun q =>
      pairBlk F T hA hC hD q.1 (hJ.valid _ (Multiset.mem_of_mem_filter q.2))
        (hJ.unit _ (Multiset.mem_of_mem_filter q.2)))) =
      (posPart F T J).attach.map fun q => q.1.rect.degree + q.1.refl.rect.degree :=
    Multiset.map_congr rfl fun q _ => by
      change 2 * _ = _
      rw [degree_rect, degree_rect]
      simp only [RParam.refl_ρ, RParam.refl_n, RParam.refl_d]
      ring
  have a1 := Multiset.attach_map_val' (zeroPart F T J)
    (fun q : RParam.{uF, max uF uV} T => q.rect.degree)
  have a2 := Multiset.attach_map_val' (posPart F T J)
    (fun q : RParam.{uF, max uF uV} T => q.rect.degree + q.refl.rect.degree)
  rw [e1, e2, a1, a2, Multiset.sum_map_add]
  conv_rhs => rw [split_family F T hJ.refl]
  rw [Multiset.map_add, Multiset.map_add, Multiset.sum_add, Multiset.sum_add,
    Multiset.map_map, add_assoc]
  rfl


/-- The blocks of a family are members of `X_k` once all base degrees are at most `k`. -/
theorem famBlocks_isTadicXBlock (J : Multiset (RParam.{uF, max uF uV} T)) (hJ : UFamily F T J)
    {k : ℕ} (hk : ∀ q ∈ J, (tadicMultisegment q.ρ q.n q.d q.hd).degree ≤ k) :
    ∀ b ∈ famBlocks F T hA hC hD J hJ, IsTadicXBlock k b.rep := by
  intro b hb
  rw [famBlocks, List.mem_append, List.mem_map, List.mem_map] at hb
  rcases hb with ⟨q, -, rfl⟩ | ⟨q, -, rfl⟩
  · have hq : q.1 ∈ J := Multiset.mem_of_mem_filter q.2
    have hα : q.1.α = 0 := Multiset.of_mem_filter (p := fun r : RParam.{uF, max uF uV} T =>
      r.α = 0) q.2
    have hv := hJ.valid _ hq
    have h := rectSocle_spec F T q.1
    change (tadicMultisegment (q.1.ρ.twist q.1.α) q.1.n q.1.d q.1.hd).IsZelevinskySocle _ at h
    rw [hα, CuspidalDatum.twist_zero] at h
    refine Or.inl ⟨q.1.ρ, q.1.n, q.1.d, q.1.hd, hv.2.1, hv.1, ?_, h⟩
    change q.1.rect.degree ≤ k
    rw [degree_rect]
    exact hk _ hq
  · have hq : q.1 ∈ J := Multiset.mem_of_mem_filter q.2
    have hα : 0 < q.1.α := Multiset.of_mem_filter (p := fun r : RParam.{uF, max uF uV} T =>
      0 < r.α) q.2
    have hv := hJ.valid _ hq
    have hα' : |q.1.α| < 1 / 2 := hv.2.2
    rw [abs_lt] at hα'
    have hn : 0 < q.1.n := hv.2.1
    have hρ : q.1.ρ.IsUnitary := hv.1
    have hM := baseDegree_pos F T q.1 hv
    refine Or.inr ⟨q.1.ρ, q.1.n, q.1.d, q.1.hd, (tadicMultisegment q.1.ρ q.1.n q.1.d q.1.hd).degree,
      hM, baseSocle F T q.1, q.1.α, rfl, hn, hρ, hk _ hq, baseSocle_spec F T q.1, hα, hα'.2, ?_⟩
    change Nonempty (tadicComplementaryProduct hM (baseSocle F T q.1) q.1.α ≅ pairRep F T q.1 hv)
    exact ⟨Iso.refl _⟩

/-! ### Members of `X_k` -/

theorem isIrreducible_cast {N N' : ℕ} (h : N = N')
    (X : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear N F.Carrier))
    (hX : letI := T.topology; X.IsIrreducible) : letI := T.topology; (h ▸ X).IsIrreducible := by
  subst h
  exact hX

include hA hD in
/-- **Members of `X_k`** under `(U^k)` are irreducible and their classes are products of
rectangle classes of a family. -/
theorem isTadicXBlock_analysis {k : ℕ} (hU : TadicSocleUnitarity.{uF, uV} F T k) {N : ℕ}
    {τ : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear N F.Carrier)}
    (hτ : IsTadicXBlock k τ) :
    letI := T.topology
    ∃ (hirr : τ.IsIrreducible) (J : Multiset (RParam.{uF, max uF uV} T)), UFamily F T J ∧
      cls F T τ (SmoothRep.hasFiniteLength_of_isIrreducible hirr) = (J.map (rectCls F T)).prod := by
  let := T.topology
  rcases hτ with ⟨ρ, n, d, hd, hn, hρ, hNk, hs⟩ |
    ⟨ρ, n, d, hd, M, hM, σ, α, hMN, hn, hρ, hMk, hσ, hα0, hα, ⟨eτ⟩⟩
  · let q : RParam.{uF, max uF uV} T := ⟨ρ, n, d, hd, 0⟩
    have hdeg := tadicMultisegment_rank_eq_of_isZelevinskySocle hs
    have hbase : BaseUnitary F T q := by
      intro N' X hX
      change (tadicMultisegment ρ n d hd).IsZelevinskySocle X at hX
      have := tadicMultisegment_rank_eq_of_isZelevinskySocle hX
      exact hU ρ n d hd hn hρ X (by omega) hX
    have hfam : UFamily F T {q} := by
      refine ⟨fun r hr => ?_, ?_, fun r hr => ?_⟩
      · rw [Multiset.mem_singleton] at hr; subst hr
        exact ⟨hρ, hn, by simp [q]⟩
      · rw [Multiset.map_singleton]
        congr 1
        exact RParam.ext' rfl rfl rfl (by simp [q, RParam.refl])
      · rw [Multiset.mem_singleton] at hr; subst hr; exact hbase
    have hirr := isIrreducible_of_isZelevinskySocle F T hs
    refine ⟨hirr, {q}, hfam, ?_⟩
    rw [Multiset.map_singleton, Multiset.prod_singleton]
    have hs' : q.rect.IsZelevinskySocle τ := by
      change (tadicMultisegment (ρ.twist 0) n d hd).IsZelevinskySocle τ
      rw [CuspidalDatum.twist_zero]
      exact hs
    exact cls_eq_rectCls F T hs' _
  · let q : RParam.{uF, max uF uV} T := ⟨ρ, n, d, hd, α⟩
    have hbase : BaseUnitary F T q := by
      intro N' X hX
      change (tadicMultisegment ρ n d hd).IsZelevinskySocle X at hX
      have h1 := tadicMultisegment_rank_eq_of_isZelevinskySocle hX
      have h2 := tadicMultisegment_rank_eq_of_isZelevinskySocle hσ
      exact hU ρ n d hd hn hρ X (by omega) hX
    have hσu : IsUnitarizable σ.representation := hU ρ n d hd hn hρ σ hMk hσ
    have hαabs : |α| < 1 / 2 := by rw [abs_lt]; constructor <;> linarith
    have hCirr := tadicComplementaryProduct_isIrreducible F T hM hA hD hσ hσu hαabs
    have hirr : τ.IsIrreducible :=
      SmoothRep.isIrreducible_of_iso eτ (isIrreducible_cast F T hMN _ hCirr)
    have hfam : UFamily F T {q, q.refl} := by
      refine ⟨fun r hr => ?_, ?_, fun r hr => ?_⟩
      · rw [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hr
        rcases hr with rfl | rfl
        · exact ⟨hρ, hn, hαabs⟩
        · exact ⟨hρ, hn, show |(-α)| < 1 / 2 by rw [abs_neg]; exact hαabs⟩
      · rw [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton, RParam.refl_refl,
          ← Multiset.cons_zero, ← Multiset.cons_zero, Multiset.cons_swap]
      · rw [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hr
        rcases hr with rfl | rfl
        · exact hbase
        · exact hbase
    refine ⟨hirr, {q, q.refl}, hfam, ?_⟩
    rw [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton, Multiset.prod_cons,
      Multiset.prod_singleton]
    have hσi := isIrreducible_of_isZelevinskySocle F T hσ
    have hfl := SmoothRep.hasFiniteLength_of_isIrreducible hCirr
    rw [← cls_eq_of_iso F T eτ (SmoothRep.hasFiniteLength_of_isIrreducible
        (isIrreducible_cast F T hMN _ hCirr)), cls_cast F T hMN _ hfl,
      cls_tadicComplementaryProduct F T hM σ hσi α hfl, cls_segmentFactor_eq_rectCls F T hM hσ,
      cls_segmentFactor_eq_rectCls F T hM hσ]
    rfl

end Langlands.Classification.TadicBlockBlocks
