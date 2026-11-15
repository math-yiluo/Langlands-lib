import Langlands.Representation.Classification.MoeglinWaldspurgerHeadLists

/-!
# Cutting the top cuspidal off products of segment heads

The Langlands head of a realized interval `[i, c]` with `i < c` embeds into the product of the
cuspidal `ν^{x+c} ρ` with the head of `[i, c - 1]`; the head of `[c, c]` is that cuspidal; and
heads of intervals ending at `c` commute with it. Iterating along a list of intervals ending at
`c`, the product of their heads with any `Y` embeds into `(ν^{x+c} ρ)^k × (heads of the
shortened intervals × Y)`.
-/

noncomputable section

namespace Langlands.MoeglinWaldspurger.Derivation

open CategoryTheory PadicField.TopologicalData Classification GeneralLinear
open Langlands.Classification.LeftCuspidalDerivative

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} {T : F.TopologicalData}

/-! ### Segment-level facts -/

/-- A one-term segment's supercuspidal representative is a segment head. -/
theorem singleton_isSegmentHead (κ : T.CuspidalDatum.{max uF uV, uF})
    (A : letI := T.topology
      GeneralLinear.SupercuspidalRep.{uF, max uF uV} (F := F.Carrier) (n := κ.rank))
    (hA : κ.IsRepresentedBy A) :
    T.IsSegmentHead (T.singletonSegment κ)
      (T.castRank (T.singletonSegment_degree κ).symm A.obj) := by
  let := T.topology
  let e := T.singletonSegmentInducedEquiv κ.rank_pos A.obj
  have hB := T.isIrreducible_castRank (T.singletonSegment_degree κ).symm A.obj A.property.1
  exact ⟨A, hA, (Classification.isIrreducibleHead_self _ hB).of_equiv e.symm⟩

/-- Segment heads of equal segments agree up to rank transport. -/
theorem castIso_heads_of_eq {Δ Γ : T.Segment.{max uF uV, uF}} (h : Δ = Γ)
    {Z : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier)}
    {Z' : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Γ.degree F.Carrier)}
    (hZ : T.IsSegmentHead Δ Z) (hZ' : T.IsSegmentHead Γ Z') : CastIso T Z Z' := by
  subst h
  obtain ⟨e⟩ := hZ.nonempty_iso_segmentHead
  obtain ⟨e'⟩ := hZ'.nonempty_iso_segmentHead
  exact castIso_of_iso (e ≪≫ e'.symm)

/-- **Head cut** for a segment `⟨κ, 1 + b⟩`. -/
theorem headCut_embeds {κ : T.CuspidalDatum.{max uF uV, uF}} {b : ℕ} (hb : 0 < b)
    {Z : letI := T.topology;
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear ((1 + b) * κ.rank) F.Carrier)}
    (hZ : T.IsSegmentHead ⟨κ, 1 + b, by omega⟩ Z)
    {Z₂ : letI := T.topology;
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (b * κ.rank) F.Carrier)}
    (hZ₂ : T.IsSegmentHead ⟨κ, b, hb⟩ Z₂)
    (A : letI := T.topology
      GeneralLinear.SupercuspidalRep.{uF, max uF uV} (F := F.Carrier) (n := κ.rank))
    (hA : (κ.twist ((b : ℕ) : ℝ)).IsRepresentedBy A) :
    letI := T.topology
    Embeds T Z ((T.binaryNormalizedProductFunctor κ.rank (b * κ.rank)).obj (A.obj, Z₂)) := by
  let := T.topology
  have hZ₁ := singleton_isSegmentHead (κ.twist ((b : ℕ) : ℝ)) A hA
  obtain ⟨j, hj⟩ := SegmentHeadCut.headCutEmbedding T κ 1 b Nat.one_pos hb hZ hZ₁ hZ₂
    κ.representative κ.isRepresentedBy_representative
  have hemb : Embeds T Z ((T.binaryNormalizedProductFunctor (1 * κ.rank) (b * κ.rank)).obj
      (T.castRank (T.singletonSegment_degree (κ.twist ((b : ℕ) : ℝ))).symm A.obj, Z₂)) :=
    embeds_of_isSubrepresentation_rankCast (Nat.add_mul 1 b κ.rank).symm
      ⟨SmoothRep.ofHom j, hj⟩
  have hc : CastIso T
      ((T.binaryNormalizedProductFunctor (1 * κ.rank) (b * κ.rank)).obj
        (T.castRank (T.singletonSegment_degree (κ.twist ((b : ℕ) : ℝ))).symm A.obj, Z₂))
      ((T.binaryNormalizedProductFunctor κ.rank (b * κ.rank)).obj (A.obj, Z₂)) :=
    (castIso_castRank _ A.obj).symm.binary (CastIso.refl Z₂)
  exact hemb.castIso_right hc

/-- **Head cut** for a general segment of length `1 + b`. -/
theorem headCut_embeds' {Δ Γ : T.Segment.{max uF uV, uF}} {b : ℕ} (hb : 0 < b)
    (hm : Δ.length = 1 + b) (hΓ : Γ = ⟨Δ.base, b, hb⟩)
    {Z : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier)}
    (hZ : T.IsSegmentHead Δ Z)
    {Z₂ : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Γ.degree F.Carrier)}
    (hZ₂ : T.IsSegmentHead Γ Z₂)
    (A : letI := T.topology
      GeneralLinear.SupercuspidalRep.{uF, max uF uV} (F := F.Carrier) (n := Δ.rank))
    (hA : (Δ.base.twist ((b : ℕ) : ℝ)).IsRepresentedBy A) :
    letI := T.topology
    Embeds T Z ((T.binaryNormalizedProductFunctor Δ.rank Γ.degree).obj (A.obj, Z₂)) := by
  subst hΓ
  obtain ⟨κ, l, hl⟩ := Δ
  simp only at hm
  subst hm
  exact headCut_embeds hb hZ hZ₂ A hA

/-! ### Interval-level facts -/

/-- `[i, e]` shortened to `[i, e - 1]`. -/
def shortR (I : Interval) (h : I.beginning < I.ending) : Interval :=
  ⟨I.beginning, I.ending - 1, by omega⟩

variable (ρ : T.CuspidalDatum.{max uF uV, uF}) (x : ℝ)

theorem pointBlock_isSegmentHead (y : ℤ) :
    T.IsSegmentHead (pointSegment ρ x y) (pointBlock F ρ x y) :=
  singleton_isSegmentHead _ _ (cuspRep_represents F T ρ x y)

/-- The head of `[i, c]`, `i < c`, embeds into `ν^{x+c} ρ × L([i, c - 1])`. -/
theorem segHead_cut (I : Interval) (h : I.beginning < I.ending) (c : ℤ) (hc : I.ending = c) :
    letI := T.topology
    Embeds T (segHead F ρ x I)
      ((T.binaryNormalizedProductFunctor ρ.rank ((shortR I h).realize ρ x).degree).obj
        ((cuspRep F T ρ x c).obj, segHead F ρ x (shortR I h))) := by
  let := T.topology
  subst hc
  have hlen : I.length = 1 + (shortR I h).length := by
    simp only [Interval.length, shortR]
    omega
  have hbz : (((shortR I h).length : ℕ) : ℤ) = I.ending - I.beginning := by
    simp only [Interval.length, shortR]
    omega
  have hbr : (((shortR I h).length : ℕ) : ℝ) = ((I.ending : ℤ) : ℝ) - ((I.beginning : ℤ) : ℝ) := by
    rw [← Int.cast_natCast, hbz, Int.cast_sub]
  have hreal : (((shortR I h).length : ℕ) : ℝ) + (x + ((I.beginning : ℤ) : ℝ)) =
      x + ((I.ending : ℤ) : ℝ) := by
    rw [hbr]
    ring
  have hA : ((I.realize ρ x).base.twist (((shortR I h).length : ℕ) : ℝ)).IsRepresentedBy
      (cuspRep F T ρ x I.ending) := by
    have h1 := cuspRep_represents F T ρ x I.ending
    show (cuspRep F T ρ x I.ending).isoClass = T.supercuspidalClassRealPowerTwist ρ.rank
      (((shortR I h).length : ℕ) : ℝ)
      (T.supercuspidalClassRealPowerTwist ρ.rank (x + ((I.beginning : ℤ) : ℝ)) ρ.cls)
    rw [T.supercuspidalClassRealPowerTwist_add, hreal]
    exact h1
  exact headCut_embeds' (shortR I h).length_pos hlen rfl (segHead_isSegmentHead ρ x I)
    (segHead_isSegmentHead ρ x (shortR I h)) (cuspRep F T ρ x I.ending) hA

/-- The head of `[c, c]` is the cuspidal `ν^{x+c} ρ`. -/
theorem segHead_point (I : Interval) (c : ℤ) (hb : I.beginning = c) (hc : I.ending = c) :
    CastIso T (segHead F ρ x I) (cuspRep F T ρ x c).obj := by
  have hI : I = point c := Interval.ext hb hc
  have hseg : I.realize ρ x = pointSegment ρ x c :=
    (congrArg (Interval.realize ρ x) hI).trans (pointSegment_eq ρ x c).symm
  exact (castIso_heads_of_eq hseg (segHead_isSegmentHead ρ x I)
    (pointBlock_isSegmentHead ρ x c)).trans (castIso_castRank _ _).symm

/-- Heads of intervals not linked with `[c, c]` commute with `ν^{x+c} ρ`. -/
theorem castIso_segHead_swap (I : Interval) (c : ℤ)
    (hun : ¬ ((I.beginning < c ∧ c ≤ I.ending + 1 ∧ I.ending < c) ∨
      (c < I.beginning ∧ I.beginning ≤ c + 1 ∧ c < I.ending))) :
    letI := T.topology
    CastIso T ((T.binaryNormalizedProductFunctor (I.realize ρ x).degree ρ.rank).obj
        (segHead F ρ x I, (cuspRep F T ρ x c).obj))
      ((T.binaryNormalizedProductFunctor ρ.rank (I.realize ρ x).degree).obj
        ((cuspRep F T ρ x c).obj, segHead F ρ x I)) := by
  let := T.topology
  have hun' : ¬ (I.realize ρ x).IsLinked (pointSegment ρ x c) := by
    rw [pointSegment_eq, realize_isLinked_iff F T ρ x]
    simpa [point] using hun
  have h := castIso_head_swap (segHead_isSegmentHead ρ x I) (pointBlock_isSegmentHead ρ x c) hun'
  have hP : CastIso T (pointBlock F ρ x c) (cuspRep F T ρ x c).obj := (castIso_castRank _ _).symm
  exact ((CastIso.refl _).binary hP.symm).trans (h.trans (hP.binary (CastIso.refl _)))

/-! ### Lists -/

theorem posOrIrr_listProd :
    ∀ (l : List Interval) {m : ℕ}
      (Y : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear m F.Carrier)),
      PosOrIrr T Y → PosOrIrr T (listProd F ρ x l Y)
  | [], _, _, h => h
  | I :: l, _, Y, h => by
    have h1 := posOrIrr_binary (posOrIrr_of_isIrreducible (segHead_isIrreducible ρ x I))
      (posOrIrr_listProd l Y h)
    exact h1

/-- Shorten every interval at its right end, discarding one-point intervals. -/
def shortList : List Interval → List Interval
  | [] => []
  | I :: l => if h : I.beginning < I.ending then shortR I h :: shortList l else shortList l

/-- **Cutting a list of heads.** If every interval of `l` ends at `c`, then
`L(l) × Y ↪ (ν^{x+c} ρ)^{|l|} × (L(shortList l) × Y)`, up to rank transport. -/
theorem cut_listProd (c : ℤ) :
    ∀ (l : List Interval), (∀ I ∈ l, I.ending = c) → ∀ {m : ℕ}
      (Y : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear m F.Carrier)),
      PosOrIrr T Y →
      Embeds T (listProd F ρ x l Y)
        (iterProd T (cuspRep F T ρ x c).obj l.length (listProd F ρ x (shortList l) Y))
  | [], _, _, Y, _ => (CastIso.refl Y).embeds
  | I :: l, hl, m, Y, hY => by
    let := T.topology
    have hr : 0 < ρ.rank := ρ.rank_pos
    have hIc : I.ending = c := hl I List.mem_cons_self
    have IH := cut_listProd c l (fun J hJ => hl J (List.mem_cons_of_mem _ hJ)) Y hY
    obtain ⟨Y', hY'def⟩ : ∃ Y', Y' = listProd F ρ x (shortList l) Y := ⟨_, rfl⟩
    rw [← hY'def] at IH
    have hY' : PosOrIrr T Y' := hY'def ▸ posOrIrr_listProd ρ x (shortList l) Y hY
    have e1 : Embeds T (listProd F ρ x (I :: l) Y)
        ((T.binaryNormalizedProductFunctor (I.realize ρ x).degree
          (powerRank ρ.rank l.length (listRank ρ x (shortList l) m))).obj
          (segHead F ρ x I, iterProd T (cuspRep F T ρ x c).obj l.length Y')) :=
      (CastIso.refl (segHead F ρ x I)).embeds.binary IH
    have hsw := castIso_segHead_swap ρ x I c (by have := I.nonempty; omega)
    have e2 := castIso_commute hr (realize_degree_pos ρ x I) (cuspRep F T ρ x c).obj
      (segHead F ρ x I) hsw l.length Y' hY'
    by_cases h : I.beginning < I.ending
    · have hsl : shortList (I :: l) = shortR I h :: shortList l := by simp [shortList, h]
      have hcut := segHead_cut ρ x I h c hIc
      have e3 := hcut.binary (CastIso.refl Y').embeds
      have e4 := castIso_assoc' hr (realize_degree_pos ρ x (shortR I h)) (cuspRep F T ρ x c).obj
        (segHead F ρ x (shortR I h)) Y' hY'
      have e5 := Embeds.iterProd (cuspRep F T ρ x c).obj l.length (e3.castIso_right e4)
      have e6 := castIso_iterProd_shift (cuspRep F T ρ x c).obj l.length
        ((T.binaryNormalizedProductFunctor ((shortR I h).realize ρ x).degree
          (listRank ρ x (shortList l) m)).obj (segHead F ρ x (shortR I h), Y'))
      rw [hsl]
      subst hY'def
      exact e1.trans (e2.embeds.trans (e5.castIso_right e6))
    · have hsl : shortList (I :: l) = shortList l := by simp [shortList, h]
      have hpt := segHead_point ρ x I c (by have := I.nonempty; omega) hIc
      have e3 := hpt.binary (CastIso.refl Y')
      have e5 := CastIso.iterProd (cuspRep F T ρ x c).obj l.length e3
      have e6 := castIso_iterProd_shift (cuspRep F T ρ x c).obj l.length Y'
      rw [hsl]
      subst hY'def
      exact e1.trans (e2.trans (e5.trans e6)).embeds

end Langlands.MoeglinWaldspurger.Derivation
