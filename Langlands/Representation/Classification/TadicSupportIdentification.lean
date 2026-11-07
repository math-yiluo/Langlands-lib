import Langlands.Representation.Classification.TadicSpehHeads
import Langlands.Representation.Classification.SegmentCuspidalContent
import Langlands.Representation.Classification.SegmentHeadProductCuspidalQuotient
import Langlands.Representation.Classification.SegmentSocleDerivativeConstituentSupport
import Langlands.Representation.Classification.SupercuspidalSupportUniquenessProof
import Langlands.Representation.Unitary.CentralCharacterProof

/-!
# Supports of Tadić's multisegments `a(n,d)^ρ`

A real twist `ν^s ρ` of a unitary cuspidal `ρ` is unitary only for `s = 0`.
Langlands heads and Zelevinsky socles of a multisegment have its cuspidal content
as supercuspidal support. Consequently a representation that is both a Zelevinsky
socle of `a(u,v)^τ` and a Langlands head of `a(n,d)^ρ`, with `τ`, `ρ` unitary,
has `τ = ρ` and `{u,v} = {n,d}`.
-/

noncomputable section

namespace Langlands.Classification

open CategoryTheory GeneralLinear PadicField.TopologicalData

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} {T : F.TopologicalData}

/-- A real twist of a unitary cuspidal datum is unitary only for the zero exponent:
the central character of `ν^s ρ` at the scalar uniformizer has absolute value
`q^(-r s)`. -/
theorem cuspidalDatum_twist_isUnitary_eq_zero {ρ : T.CuspidalDatum.{uV, uF}} {s : ℝ}
    (hρ : ρ.IsUnitary) (hs : (ρ.twist s).IsUnitary) : s = 0 := by
  let := T.topology
  rcases ρ with ⟨r, hr, c⟩
  induction c using Quotient.inductionOn with
  | h A =>
    let := T.generalLinearTopologicalGroup r
    let At := SupercuspidalRep.twist (T.determinantPowerCharacter r s)
      (T.isOpen_ker_determinantPowerCharacter r s)
      (T.ker_determinant_le_ker_determinantPowerCharacter r s) A
    have hA : IsUnitarizable A.obj.representation := hρ
    have hAt : IsUnitarizable At.obj.representation := hs
    obtain ⟨cA⟩ := unitarizableCentralCharacter A.obj.representation A.property.2.1
      A.property.1 hA
    obtain ⟨cAt⟩ := unitarizableCentralCharacter At.obj.representation At.property.2.1
      At.property.1 hAt
    have hAi : Representation.IsIrreducible A.obj.representation := A.property.1
    let := hAi
    have : Nontrivial A.obj :=
      IsSimpleModule.nontrivial (MonoidAlgebra ℂ (GeneralLinear r F.Carrier))
        A.obj.representation.asModule
    obtain ⟨v, hv⟩ := exists_ne (0 : A.obj)
    let z : Subgroup.center (GeneralLinear r F.Carrier) :=
      scalarToCenter (LocalFactor.PadicAbelian.uniformizerUnit T)
    have h1 := cAt.acts z v
    have h2 := cA.acts z v
    have h3 : At.obj.representation (z : GeneralLinear r F.Carrier) v =
        (T.determinantPowerCharacter r s (z : GeneralLinear r F.Carrier) : ℂ) •
          A.obj.representation (z : GeneralLinear r F.Carrier) v := rfl
    rw [h3, h2, smul_smul] at h1
    have hc : (T.determinantPowerCharacter r s (z : GeneralLinear r F.Carrier) : ℂ) *
        (cA.character z : ℂ) = cAt.character z :=
      smul_left_injective ℂ hv h1
    have hn := congrArg norm hc
    rw [norm_mul, cA.norm_eq_one, cAt.norm_eq_one, mul_one] at hn
    change ‖(T.determinantPowerCharacter r s
      (scalar (LocalFactor.PadicAbelian.uniformizerUnit T)) : ℂ)‖ = 1 at hn
    have hq : 1 < (T.residueCardinality : ℝ) := by
      exact_mod_cast T.residueCardinality_gt_one
    rw [IntegralTwistFreeness.scalar_uniformizer_value, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.rpow_pos_of_pos (lt_trans zero_lt_one hq) _)] at hn
    have hexp : -(r : ℝ) * s = 0 :=
      (Real.rpow_right_inj (lt_trans zero_lt_one hq) (ne_of_gt hq)).mp
        (by rw [Real.rpow_zero]; exact hn)
    have hr0 : (r : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hr)
    exact (mul_eq_zero.mp hexp).resolve_left (neg_ne_zero.mpr hr0)

/-- Two unitary cuspidal data that are real twists of each other are equal, and
the twist exponents agree. -/
theorem cuspidalDatum_eq_of_twist_eq_of_isUnitary {ρ τ : T.CuspidalDatum.{uV, uF}} {s t : ℝ}
    (hρ : ρ.IsUnitary) (hτ : τ.IsUnitary) (h : τ.twist s = ρ.twist t) : τ = ρ ∧ s = t := by
  have hτ' : τ = ρ.twist (-s + t) := by
    have h' := congrArg (CuspidalDatum.twist (-s)) h
    rwa [CuspidalDatum.twist_twist, CuspidalDatum.twist_twist, neg_add_cancel,
      CuspidalDatum.twist_zero] at h'
  have h0 : -s + t = 0 := cuspidalDatum_twist_isUnitary_eq_zero hρ (hτ' ▸ hτ)
  refine ⟨by rw [hτ', h0, CuspidalDatum.twist_zero], by linarith⟩

/-- The cuspidal content of `a(n,d)^ρ` consists of the twists
`ν^(i + j - (n-1)/2 - (d-1)/2) ρ` with `j < n` and `i < d`. -/
theorem mem_cuspidalContent_tadicMultisegment (ρ : T.CuspidalDatum.{uV, uF}) (n d : ℕ)
    (hd : 0 < d) (x : T.CuspidalDatum.{uV, uF}) :
    x ∈ (tadicMultisegment ρ n d hd).cuspidalContent ↔
      ∃ j < n, ∃ i < d,
        ρ.twist ((i : ℝ) + ((j : ℝ) - ((n : ℝ) - 1) / 2 - ((d : ℝ) - 1) / 2)) = x := by
  change x ∈ Multiset.join _ ↔ _
  simp only [Multiset.mem_join, tadicMultisegment, Multiset.mem_map, Multiset.mem_range]
  constructor
  · rintro ⟨_, ⟨_, ⟨j, hj, rfl⟩, rfl⟩, hx⟩
    rw [Segment.mem_cuspidalContent] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    exact ⟨j, hj, i, hi, by
      simp only [Segment.member, tadicCenteredSegment, CuspidalDatum.twist_twist]⟩
  · rintro ⟨j, hj, i, hi, rfl⟩
    refine ⟨_, ⟨_, ⟨j, hj, rfl⟩, rfl⟩, ?_⟩
    rw [Segment.mem_cuspidalContent]
    exact ⟨i, hi, by
      simp only [Segment.member, tadicCenteredSegment, CuspidalDatum.twist_twist]⟩

/-- `a(n,d)^ρ` has `n d` cuspidal members, counted with multiplicity. -/
theorem card_cuspidalContent_tadicMultisegment (ρ : T.CuspidalDatum.{uV, uF}) (n d : ℕ)
    (hd : 0 < d) : Multiset.card (tadicMultisegment ρ n d hd).cuspidalContent = n * d := by
  change Multiset.card (Multiset.join _) = n * d
  simp [Multiset.card_join, tadicMultisegment, Multiset.map_map, Function.comp_def]

/-- A Langlands head of an ordered product of segment heads has the cuspidal content
of its multisegment as a supercuspidal support. -/
theorem SegmentProductDatum.isSupercuspidalSupport_of_isLanglandsHead {N : ℕ}
    (E : T.SegmentProductDatum.{max uF uV, uF} N)
    {π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear N F.Carrier)}
    (h : E.IsLanglandsHead π) : T.IsSupercuspidalSupport π E.multisegment.cuspidalContent := by
  let := T.topology
  let C := segmentHeadProductCuspidalQuotient T E h.2.1
  obtain ⟨hπ, q, hq, -⟩ := h.2.2
  refine ⟨C.length, C.members, C.content_eq, C.rank_sum, C.representatives, C.represents,
    hπ, ?_⟩
  apply SmoothRep.IsQuotient.isSubquotient
  exact ⟨C.quotientMap ≫ SmoothRep.ofHom q, hq.comp C.surjective⟩

/-- A Zelevinsky socle of an ordered product of segment socles has the cuspidal
content of its multisegment as a supercuspidal support. -/
theorem SegmentProductDatum.isSupercuspidalSupport_of_isZelevinskySocle {N : ℕ}
    (E : T.SegmentProductDatum.{max uF uV, uF} N)
    {π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear N F.Carrier)}
    (h : E.IsZelevinskySocle π) :
    T.IsSupercuspidalSupport π E.multisegment.cuspidalContent := by
  let := T.topology
  obtain ⟨-, hs, hπ, j, hj, -⟩ := h
  exact SegmentSocleDerivativeConstituentSupport.support_of_product T E hs π hπ
    (SmoothRep.IsSubrepresentation.isSubquotient ⟨SmoothRep.ofHom j, hj⟩)

/-- Langlands heads of a multisegment have its cuspidal content as support. -/
theorem isSupercuspidalSupport_of_isLanglandsHead {N : ℕ} {a : T.Multisegment.{max uF uV, uF}}
    {π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear N F.Carrier)}
    (h : a.IsLanglandsHead π) : T.IsSupercuspidalSupport π a.cuspidalContent := by
  obtain ⟨E, rfl, hE⟩ := h
  exact SegmentProductDatum.isSupercuspidalSupport_of_isLanglandsHead E hE

/-- Zelevinsky socles of a multisegment have its cuspidal content as support. -/
theorem isSupercuspidalSupport_of_isZelevinskySocle {N : ℕ}
    {a : T.Multisegment.{max uF uV, uF}}
    {π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear N F.Carrier)}
    (h : a.IsZelevinskySocle π) : T.IsSupercuspidalSupport π a.cuspidalContent := by
  obtain ⟨E, rfl, hE⟩ := h
  exact SegmentProductDatum.isSupercuspidalSupport_of_isZelevinskySocle E hE

/-- The largest exponent of the cuspidal content of `a(u,v)^ρ` is at most that of
any `a(n,d)^ρ` with the same cuspidal content. -/
theorem tadicMaxExponent_le_of_cuspidalContent_eq (ρ : T.CuspidalDatum.{uV, uF})
    {u v n d : ℕ} (hu : 0 < u) (hv : 0 < v) (hd : 0 < d)
    (h : (tadicMultisegment ρ u v hv).cuspidalContent =
      (tadicMultisegment ρ n d hd).cuspidalContent) :
    ((u : ℝ) - 1) / 2 + ((v : ℝ) - 1) / 2 ≤ ((n : ℝ) - 1) / 2 + ((d : ℝ) - 1) / 2 := by
  have hm : ρ.twist ((((v - 1 : ℕ) : ℝ)) + ((((u - 1 : ℕ) : ℝ)) - ((u : ℝ) - 1) / 2 -
      ((v : ℝ) - 1) / 2)) ∈ (tadicMultisegment ρ u v hv).cuspidalContent :=
    (mem_cuspidalContent_tadicMultisegment ρ u v hv _).mpr
      ⟨u - 1, by omega, v - 1, by omega, rfl⟩
  rw [h, mem_cuspidalContent_tadicMultisegment] at hm
  obtain ⟨j, hj, i, hi, hji⟩ := hm
  have hx := cuspidalDatum_twist_injective ρ hji
  rw [Nat.cast_pred hu, Nat.cast_pred hv] at hx
  have hj' : (j : ℝ) + 1 ≤ n := by exact_mod_cast hj
  have hi' : (i : ℝ) + 1 ≤ d := by exact_mod_cast hi
  linarith

/-- Equal cuspidal contents of `a(u,v)^τ` and `a(n,d)^ρ`, for unitary `τ` and `ρ`,
force `τ = ρ` and `{u,v} = {n,d}`. -/
theorem tadic_parameters_of_cuspidalContent_eq {ρ τ : T.CuspidalDatum.{uV, uF}}
    (hρ : ρ.IsUnitary) (hτ : τ.IsUnitary) {u v n d : ℕ} (hu : 0 < u) (hv : 0 < v)
    (hn : 0 < n) (hd : 0 < d)
    (h : (tadicMultisegment τ u v hv).cuspidalContent =
      (tadicMultisegment ρ n d hd).cuspidalContent) :
    τ = ρ ∧ ((u = n ∧ v = d) ∨ (u = d ∧ v = n)) := by
  have hmem : τ.twist (((0 : ℕ) : ℝ) + (((0 : ℕ) : ℝ) - ((u : ℝ) - 1) / 2 -
      ((v : ℝ) - 1) / 2)) ∈ (tadicMultisegment τ u v hv).cuspidalContent :=
    (mem_cuspidalContent_tadicMultisegment τ u v hv _).mpr ⟨0, hu, 0, hv, rfl⟩
  rw [h, mem_cuspidalContent_tadicMultisegment] at hmem
  obtain ⟨j, -, i, -, hji⟩ := hmem
  obtain ⟨rfl, -⟩ := cuspidalDatum_eq_of_twist_eq_of_isUnitary hρ hτ hji.symm
  refine ⟨rfl, ?_⟩
  have h₁ := tadicMaxExponent_le_of_cuspidalContent_eq τ hu hv hd h
  have h₂ := tadicMaxExponent_le_of_cuspidalContent_eq τ hn hd hv h.symm
  have hsum : (u : ℤ) + v = n + d := by
    have : (u : ℝ) + v = n + d := by linarith
    exact_mod_cast this
  have hprod : (u : ℤ) * v = n * d := by
    have := congrArg Multiset.card h
    rw [card_cuspidalContent_tadicMultisegment, card_cuspidalContent_tadicMultisegment] at this
    exact_mod_cast this
  have hfac : ((u : ℤ) - n) * ((u : ℤ) - d) = 0 := by
    linear_combination (u : ℤ) * hsum - hprod
  rcases mul_eq_zero.mp hfac with h0 | h0
  · left
    omega
  · right
    omega

/-- A representation that is both a Zelevinsky socle of `a(u,v)^τ` and a Langlands head
of `a(n,d)^ρ`, with `τ` and `ρ` unitary, has `τ = ρ` and `{u,v} = {n,d}`. -/
theorem tadic_parameters_of_isZelevinskySocle_of_isLanglandsHead
    {ρ τ : T.CuspidalDatum.{max uF uV, uF}} (hρ : ρ.IsUnitary) (hτ : τ.IsUnitary)
    {u v n d : ℕ} (hu : 0 < u) (hv : 0 < v) (hn : 0 < n) (hd : 0 < d) {N : ℕ}
    {π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear N F.Carrier)}
    (hs : (tadicMultisegment τ u v hv).IsZelevinskySocle π)
    (hh : (tadicMultisegment ρ n d hd).IsLanglandsHead π) :
    τ = ρ ∧ ((u = n ∧ v = d) ∨ (u = d ∧ v = n)) := by
  let := T.topology
  have hN : 0 < N := by
    rw [tadicMultisegment_rank_eq_of_isZelevinskySocle hs]
    exact Nat.mul_pos hu (Nat.mul_pos hv τ.rank_pos)
  have hπ : π.IsIrreducible := by
    obtain ⟨E, -, -, -, hπ, -⟩ := hh
    exact hπ
  have heq := glSupercuspidalSupportUniqueness.{max uF uV, uF} p F T N hN π hπ _ _
    (isSupercuspidalSupport_of_isZelevinskySocle hs)
    (isSupercuspidalSupport_of_isLanglandsHead hh)
  exact tadic_parameters_of_cuspidalContent_eq hρ hτ hu hv hn hd heq

end Langlands.Classification
