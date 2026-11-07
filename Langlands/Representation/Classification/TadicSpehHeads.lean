import Langlands.Representation.Classification.TadicMultisegments
import Langlands.Representation.Classification.SegmentSocleInversionReduction
import Langlands.Representation.Classification.SpehLanglandsAdapters
import Langlands.Representation.Classification.OrderedSegmentHeadProductIndependence
import Langlands.Representation.Classification.SegmentConstituentRealTwistCompatibilityProof
import Langlands.Representation.Classification.SegmentSpecialConstituentExistenceProof
import Langlands.Representation.Classification.SegmentCenteredSpecialSquareIntegrabilityProof
import Langlands.Representation.Classification.CuspidalIntegralTwistFreenessProof
import Langlands.Representation.Classification.RegularLanglandsHeadExistenceProof

/-!
# Langlands heads of `a(d,n)^ρ` are Speh representations

For a unitary cuspidal `ρ`, the multisegment `a(d,n)^ρ` consists of the `d`
segments `ν^x Δ[n]^ρ` with centers `x = (d-1)/2 - i`. Listing them with
decreasing centers gives a precedence-ordered product of segment heads which
is exactly the centered Speh induction of `δ = L(Δ[n]^ρ)`. Hence every
Langlands head of `a(d,n)^ρ` is a Speh representation `u(δ,d)`.
-/

noncomputable section

namespace Langlands.Classification

open CategoryTheory GeneralLinear PadicField.TopologicalData

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} {T : F.TopologicalData}

/-- A real determinant twist fixes a cuspidal datum only for the zero exponent. -/
theorem cuspidalDatum_twist_eq_self {ρ : T.CuspidalDatum.{uV, uF}} {s : ℝ}
    (h : ρ.twist s = ρ) : s = 0 := by
  let := T.topology
  rcases ρ with ⟨r, hr, c⟩
  have hc : T.supercuspidalClassRealPowerTwist r s c = c := by
    simpa only [CuspidalDatum.twist, CuspidalDatum.mk.injEq, heq_eq_eq, true_and] using h
  induction c using Quotient.inductionOn with
  | h A =>
    let At := SupercuspidalRep.twist (T.determinantPowerCharacter r s)
      (T.isOpen_ker_determinantPowerCharacter r s)
      (T.ker_determinant_le_ker_determinantPowerCharacter r s) A
    change At.isoClass = A.isoClass at hc
    obtain ⟨e⟩ := (SupercuspidalRep.isoClass_eq_iff At A).mp hc
    let e' := SmoothRep.equivOfIso ((supercuspidalProperty (F := F.Carrier)
      (n := r)).ι.mapIso e.symm)
    exact IntegralTwistFreeness.exponent_eq_zero_of_equiv T r hr A.obj
      A.property.2.1 A.property.1 s e'

/-- Real twists of one cuspidal datum are pairwise distinct. -/
theorem cuspidalDatum_twist_injective (ρ : T.CuspidalDatum.{uV, uF}) {s t : ℝ}
    (h : ρ.twist s = ρ.twist t) : s = t := by
  have h' : (ρ.twist s).twist (-t) = (ρ.twist t).twist (-t) := by rw [h]
  rw [CuspidalDatum.twist_twist, CuspidalDatum.twist_twist, neg_add_cancel,
    CuspidalDatum.twist_zero] at h'
  have := cuspidalDatum_twist_eq_self h'
  linarith

/-- `ν^x Δ[n]^ρ` is the twist of `Δ[n]^ρ` by `ν^x`. -/
theorem tadicCenteredSegment_eq_twist (ρ : T.CuspidalDatum.{uV, uF}) (n : ℕ) (hn : 0 < n)
    (x : ℝ) : tadicCenteredSegment ρ n hn x = (tadicCenteredSegment ρ n hn 0).twist x := by
  simp only [tadicCenteredSegment, Segment.twist, CuspidalDatum.twist_twist]
  congr 2
  ring

/-- The segments of `a(d,n)^ρ` listed with decreasing centers `(d-1)/2 - i`. -/
def spehSegments (ρ : T.CuspidalDatum.{uV, uF}) (n d : ℕ) (hn : 0 < n) :
    Fin d → T.Segment.{uV, uF} :=
  fun i => (tadicCenteredSegment ρ n hn 0).twist (((d : ℝ) - 1) / 2 - (i : ℕ))

theorem spehSegments_multiset (ρ : T.CuspidalDatum.{uV, uF}) (n d : ℕ) (hn : 0 < n) :
    (List.ofFn (spehSegments ρ n d hn) : Multiset (T.Segment.{uV, uF})) =
      tadicMultisegment ρ d n hn := by
  let g : ℕ → T.Segment.{uV, uF} := fun j =>
    tadicCenteredSegment ρ n hn ((j : ℝ) - ((d : ℝ) - 1) / 2)
  have hs : spehSegments ρ n d hn = (fun i : Fin d => g i) ∘ Fin.rev := by
    funext i
    have hi : (i : ℕ) + 1 ≤ d := i.isLt
    simp only [spehSegments, g, Function.comp_apply, Fin.val_rev, tadicCenteredSegment,
      Segment.twist, CuspidalDatum.twist_twist]
    congr 2
    rw [Nat.cast_sub hi]
    push_cast
    ring
  have hr : (Finset.univ.val.map Fin.rev : Multiset (Fin d)) = Finset.univ.val :=
    Multiset.map_univ_val_equiv Fin.revPerm
  have hl : List.ofFn (fun i : Fin d => g i) = List.map g (List.range d) :=
    List.ext_getElem (by simp) fun k h₁ h₂ => by simp
  rw [hs, ← Fin.univ_val_map, ← Multiset.map_map, hr, Fin.univ_val_map, hl]
  rfl

/-- A Langlands head of `a(d,n)^ρ` on `GL_N` has `N = d n deg ρ`. -/
theorem tadicMultisegment_rank_eq_of_isLanglandsHead {ρ : T.CuspidalDatum.{max uF uV, uF}}
    {n d : ℕ} {hn : 0 < n} {N : ℕ}
    {π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear N F.Carrier)}
    (h : (tadicMultisegment ρ d n hn).IsLanglandsHead π) : N = d * (n * ρ.rank) := by
  obtain ⟨E, hE, -⟩ := h
  have hdeg := PadicField.TopologicalData.SegmentProductDatum.multisegment_degree E
  rw [hE, tadicMultisegment_degree] at hdeg
  exact hdeg.symm

section SpehDatum

variable (ρ : T.CuspidalDatum.{max uF uV, uF}) {n : ℕ} (hn : 0 < n)

/-- A chosen strong segment head `δ = L(Δ[n]^ρ)` of the centered segment
`ν^0 Δ[n]^ρ` (it exists by `segmentSpecialConstituentExistence`). -/
def tadicSegmentHead :
    letI := T.topology
    SmoothRep.{0, uF, max uF uV} ℂ
      (GeneralLinear (tadicCenteredSegment ρ n hn 0).degree F.Carrier) :=
  letI := T.topology
  (segmentSpecialConstituentExistence.{uF, max uF uV} F T
    (tadicCenteredSegment ρ n hn 0)).choose

theorem isSegmentHead_tadicSegmentHead :
    T.IsSegmentHead (tadicCenteredSegment ρ n hn 0) (tadicSegmentHead ρ hn) :=
  letI := T.topology
  (segmentSpecialConstituentExistence.{uF, max uF uV} F T
    (tadicCenteredSegment ρ n hn 0)).choose_spec.1

/-- The Speh datum `(δ, d)` with `δ = L(Δ[n]^ρ)`. -/
def tadicSpehDatum (d : ℕ) (hd : 0 < d) : SpehDatum.{uF, uV} F T where
  rank := (tadicCenteredSegment ρ n hn 0).degree
  rank_pos := (tadicCenteredSegment ρ n hn 0).degree_pos
  length := d
  length_pos := hd
  delta := tadicSegmentHead ρ hn

/-- For unitary `ρ`, `L(Δ[n]^ρ)` is irreducible, unitarizable and square-integrable. -/
theorem tadicSpehDatum_isDiscreteSeries (hρ : ρ.IsUnitary) (d : ℕ) (hd : 0 < d) :
    (tadicSpehDatum ρ hn d hd).IsDiscreteSeries := by
  let := T.topology
  let Δ₀ := tadicCenteredSegment ρ n hn 0
  let δ := tadicSegmentHead ρ hn
  have hδ : T.IsSegmentHead Δ₀ δ := isSegmentHead_tadicSegmentHead ρ hn
  -- Center the twist `ν^c δ`, `c = (n-1)/2`.
  let c : ℝ := ((n : ℝ) - 1) / 2
  have hδc : T.IsSegmentHead (Δ₀.twist c) (T.segmentFactor δ c) :=
    ((segmentConstituentRealTwistCompatibility.{uF, max uF uV} F T Δ₀ c δ).2.1).mp hδ
  obtain ⟨A, hA⟩ := Quotient.exists_rep ρ.cls
  have hAρ : ρ.IsRepresentedBy A := hA
  have hcls : (Δ₀.twist c).base.cls = ρ.cls := by
    change T.supercuspidalClassRealPowerTwist ρ.rank c
      (T.supercuspidalClassRealPowerTwist ρ.rank (0 - c) ρ.cls) = ρ.cls
    rw [T.supercuspidalClassRealPowerTwist_add, show c + (0 - c) = 0 by ring,
      T.supercuspidalClassRealPowerTwist_zero]
  have hAΔ : (Δ₀.twist c).base.IsRepresentedBy A := hAρ.trans hcls.symm
  have hAu : IsUnitarizable A.obj.representation := by
    have hu : GeneralLinear.SupercuspidalClass.IsUnitarizable A.isoClass := by
      rw [show A.isoClass = ρ.cls from hAρ]
      exact hρ
    exact hu
  have hquot : T.IsSegmentQuotient (Δ₀.twist c) (T.segmentFactor δ c) := by
    obtain ⟨A', hA', hπ', q, hq, -⟩ := hδc
    exact ⟨A', hA', hπ', q, hq⟩
  have hsi := segmentCenteredSpecialSquareIntegrability.{uF, uV} F T (Δ₀.twist c) A hAΔ hAu _
    hquot
  have hsq : T.IsSquareIntegrable δ.representation := by
    have h₁ := hsi.1
    change T.IsSquareIntegrable (realPowerTwist (T.determinantNorm Δ₀.degree) (-c)
      (realPowerTwist (T.determinantNorm Δ₀.degree) c δ.representation)) at h₁
    rwa [realPowerTwist_neg_cancel] at h₁
  have hun : IsUnitarizable δ.representation := by
    have h₁ := hsi.2
    change IsUnitarizable (realPowerTwist (T.determinantNorm Δ₀.degree) (-c)
      (realPowerTwist (T.determinantNorm Δ₀.degree) c δ.representation)) at h₁
    rwa [realPowerTwist_neg_cancel] at h₁
  have hirr : Representation.IsIrreducible δ.representation := by
    obtain ⟨A', -, hπ', -⟩ := hδ
    exact hπ'
  exact ⟨hirr, hun, hsq⟩

/-- The precedence-ordered segment datum `ν^((d-1)/2-i) Δ[n]^ρ` with blocks
`ν^((d-1)/2-i) δ`, whose induced representation is `(tadicSpehDatum ρ hn d hd).centeredInduced`. -/
def tadicSpehSegmentDatum (d : ℕ) (hd : 0 < d) :
    T.SegmentProductDatum.{max uF uV, uF} (d * (n * ρ.rank)) where
  length := d
  segments := spehSegments ρ n d hn
  degree_sum := by
    change ∑ _i : Fin d, n * ρ.rank = d * (n * ρ.rank)
    simp
  blocks := fun i =>
    letI := T.topology
    T.segmentFactor (tadicSegmentHead ρ hn) ((tadicSpehDatum ρ hn d hd).exponent i)

theorem tadicSpehSegmentDatum_induced (d : ℕ) (hd : 0 < d) :
    (tadicSpehSegmentDatum ρ hn d hd).induced = (tadicSpehDatum ρ hn d hd).centeredInduced :=
  rfl

theorem tadicSpehSegmentDatum_multisegment (d : ℕ) (hd : 0 < d) :
    (tadicSpehSegmentDatum ρ hn d hd).multisegment = tadicMultisegment ρ d n hn :=
  spehSegments_multiset ρ n d hn

theorem tadicSpehSegmentDatum_isPrecedenceOrdered (d : ℕ) (hd : 0 < d) :
    (tadicSpehSegmentDatum ρ hn d hd).IsPrecedenceOrdered := by
  intro i j hij hprec
  obtain ⟨-, k, hk, hkeq⟩ := hprec
  change (spehSegments ρ n d hn j).base = (spehSegments ρ n d hn i).base.twist (k : ℝ)
    at hkeq
  simp only [spehSegments, tadicCenteredSegment, Segment.twist,
    CuspidalDatum.twist_twist] at hkeq
  have hx := cuspidalDatum_twist_injective ρ hkeq
  have hij' : ((i : ℕ) : ℝ) < ((j : ℕ) : ℝ) := by exact_mod_cast hij
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  linarith

theorem tadicSpehSegmentDatum_hasSegmentHeads (d : ℕ) (hd : 0 < d) :
    (tadicSpehSegmentDatum ρ hn d hd).HasSegmentHeads := fun i =>
  letI := T.topology
  ((segmentConstituentRealTwistCompatibility.{uF, max uF uV} F T
    (tadicCenteredSegment ρ n hn 0) ((tadicSpehDatum ρ hn d hd).exponent i)
    (tadicSegmentHead ρ hn)).2.1).mp (isSegmentHead_tadicSegmentHead ρ hn)

end SpehDatum

/-- Tadić A.9 in Langlands form: for a unitary cuspidal `ρ`, every Langlands head of
`a(d,n)^ρ` is a Speh representation `u(δ,d)`, where `δ` is the head of `Δ[n]^ρ`. -/
theorem exists_isSpeh_of_isLanglandsHead {ρ : T.CuspidalDatum.{max uF uV, uF}}
    (hρ : ρ.IsUnitary) {n d : ℕ} (hn : 0 < n) (hd : 0 < d) {N : ℕ}
    {π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear N F.Carrier)}
    (h : (tadicMultisegment ρ d n hn).IsLanglandsHead π) :
    letI := T.topology
    ∃ (D : SpehDatum.{uF, uV} F T)
      (S : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear D.degree F.Carrier))
      (hD : D.degree = N), D.IsSpeh S ∧ Nonempty ((hD ▸ S) ≅ π) := by
  let := T.topology
  have hN := tadicMultisegment_rank_eq_of_isLanglandsHead h
  subst hN
  obtain ⟨E, hEm, hEo, hEh, hEhead⟩ := h
  let D := tadicSpehDatum ρ hn d hd
  have hDS : D.IsDiscreteSeries := tadicSpehDatum_isDiscreteSeries ρ hn hρ d hd
  let E₀ := tadicSpehSegmentDatum ρ hn d hd
  obtain ⟨e⟩ := orderedSegmentHeadProductIndependence F T _ E₀ E
    (tadicSpehSegmentDatum_isPrecedenceOrdered ρ hn d hd) hEo
    (tadicSpehSegmentDatum_hasSegmentHeads ρ hn d hd) hEh
    ((tadicSpehSegmentDatum_multisegment ρ hn d hd).trans hEm.symm)
  have hhead : IsIrreducibleHead E₀.induced.representation π.representation :=
    hEhead.of_equiv (SmoothRep.equivOfIso e).symm
  exact ⟨D, π, rfl, D.isSpeh_of_isLanglandsHead hDS hhead, ⟨Iso.refl _⟩⟩

/-- For a unitary cuspidal `ρ`, `a(d,n)^ρ` has a Langlands head: the strong
Langlands head of the centered Speh standard module, which exists by the proved
`glRegularLanglandsHeadExistence`. -/
theorem exists_isLanglandsHead_tadicMultisegment {ρ : T.CuspidalDatum.{max uF uV, uF}}
    (hρ : ρ.IsUnitary) {n d : ℕ} (hn : 0 < n) (hd : 0 < d) {N : ℕ}
    (hN : (tadicMultisegment ρ d n hn).degree = N) :
    letI := T.topology
    ∃ π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear N F.Carrier),
      (tadicMultisegment ρ d n hn).IsLanglandsHead π := by
  let := T.topology
  rw [tadicMultisegment_degree] at hN
  subst hN
  let D := tadicSpehDatum ρ hn d hd
  have hDS : D.IsDiscreteSeries := tadicSpehDatum_isDiscreteSeries ρ hn hρ d hd
  obtain ⟨π, hπ⟩ := glRegularLanglandsHeadExistence.{uF, uV} p F T D.degree D.degree_pos
    (D.temperedLanglandsDatum hDS)
  exact ⟨π, tadicSpehSegmentDatum ρ hn d hd, tadicSpehSegmentDatum_multisegment ρ hn d hd,
    tadicSpehSegmentDatum_isPrecedenceOrdered ρ hn d hd,
    tadicSpehSegmentDatum_hasSegmentHeads ρ hn d hd, hπ⟩

end Langlands.Classification
