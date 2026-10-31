import Langlands.Representation.Classification.JuxtaposedRefinementTools
import Langlands.Representation.Classification.LanglandsData
import Langlands.Representation.Classification.SegmentSocleDecreasingHead
import Langlands.Representation.Parabolic.InducedMapSurjectivity

/-! Quotients of the decreasing induction of a juxtaposed union. -/

noncomputable section

set_option maxHeartbeats 800000

namespace Langlands.Classification.JuxtaposedShuffle

open CategoryTheory GeneralLinear Geometric PadicField.TopologicalData Finset

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

/-- The product of the supplied segment socles is an actual quotient of the full
 decreasing induction, conditional only on individual-segment constituent existence. -/
theorem exists_surjective_from_decreasing
    (hex : SegmentZelevinskyConstituentExistence.{uF,uV} F T) (ρ : CuspidalDatum.{uV, uF} T)
    (A : letI := T.topology; SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := ρ.rank))
    (hA : ρ.IsRepresentedBy A) (q l : ℕ)
    (d : T.SegmentProductDatum.{uV, uF} ((q + l) * ρ.rank)) (h₂ : d.length = 2)
    (hd : d.HasSegmentSocles)
    (hb₀ : (d.segments ⟨0, by omega⟩).base = ρ.twist l)
    (hl₀ : (d.segments ⟨0, by omega⟩).length = q)
    (hb₁ : (d.segments ⟨1, by omega⟩).base = ρ.twist 0)
    (hl₁ : (d.segments ⟨1, by omega⟩).length = l) :
    letI := T.topology
    ∃ Q : (T.segmentInducedDown A.obj (q + l) ρ.rank_pos).representation.IntertwiningMap
      d.induced.representation, Function.Surjective Q := by
  let := T.topology
  obtain ⟨len, segs, hsum, blocks⟩ := d
  change len = 2 at h₂
  subst h₂
  simp only [Fin.zero_eta, Fin.mk_one] at hb₀ hl₀ hb₁ hl₁
  let a : Fin 2 → ℝ := ![(l : ℝ), 0]
  have hb : ∀ j, (segs j).base = ρ.twist (a j) := by
    intro j
    fin_cases j
    · exact hb₀
    · exact hb₁
  have hrank : ∀ j, ρ.rank = (segs j).rank := fun j => by
    rw [Segment.rank, hb j]
    rfl
  choose A' hA' hsoc using hd
  have hs : ∀ j, T.IsSegmentSocle (segs j) (blocks j) :=
    fun j => ⟨A' j, hA' j, hsoc j⟩
  let Q := fun j => (hs j).decreasingHeadQuotient hex (A' j) (hA' j)
  let J := T.normalizedProductInducedMap (T.segmentShape segs hsum) (fun j => (Q j).1)
  have hJ : Function.Surjective J := normalizedProductMap_surjective F T
    (T.segmentShape segs hsum)
    (fun j => T.segmentInducedDown (A' j).obj (segs j).length (segs j).rank_pos)
    blocks (fun j => (Q j).1) (fun j => (Q j).2)
  let B := BlockShape.uniform (q + l) ρ.rank ρ.rank_pos
  let D := T.segmentShape segs hsum
  let S : BlockRefinement D := fun j =>
    BlockShape.uniform (segs j).length (segs j).rank (segs j).rank_pos
  have hlen : ∑ j, (S j).length = q + l := by
    change ∑ j, (segs j).length = q + l
    rw [Fin.sum_univ_two, hl₀, hl₁]
  let e : ((j : Fin D.length) × Fin (S j).length) ≃ Fin B.length :=
    finSigmaFinEquiv.trans (finCongr hlen)
  have he : ∀ x y, e x < e y ↔ x.1 < y.1 ∨ (x.1 = y.1 ∧ x.2.val < y.2.val) := by
    intro x y
    simp only [e, Equiv.trans_apply]
    exact BlockShape.finSigmaFinEquiv_lt_iff x y
  have hsz : ∀ x : (j : Fin D.length) × Fin (S j).length, (S x.1).size x.2 = B.size (e x) :=
    fun x => (hrank x.1).symm
  let σ := T.segmentFactorsDown A.obj (q + l) ρ.rank_pos
  let e' : ((j : Fin D.length) × Fin (S j).length) ≃ Fin (q + l) :=
    finSigmaFinEquiv.trans (finCongr hlen)
  have hexp : ∀ x : (j : Fin D.length) × Fin (S j).length,
      ((q + l - 1 - (e' x : ℕ) : ℕ) : ℝ) =
        (((segs x.1).length - 1 - (x.2 : ℕ) : ℕ) : ℝ) + a x.1 := by
    rintro ⟨j, k⟩
    have hk := k.isLt
    change (k : ℕ) < (segs j).length at hk
    have hv : ((e' ⟨j, k⟩ : Fin (q + l)) : ℕ) =
        (if j.val = 0 then 0 else (S (0 : Fin 2)).length) + k :=
      val_finSigmaFinEquiv_fin_two (n := fun j => (S j).length) ⟨j, k⟩
    have hS0 : (S (0 : Fin 2)).length = q := hl₀
    rw [hS0] at hv
    have hj : j.val < 2 := j.isLt
    rcases (show j.val = 0 ∨ j.val = 1 by omega) with h0 | h1
    · have hj0 : @Eq (Fin 2) j 0 := Fin.ext h0
      have hsj : (segs j).length = q := by rw [hj0]; exact hl₀
      simp only [h0, ↓reduceIte, zero_add] at hv
      have ha : a j = l := by
        change ![(l : ℝ), 0] j = l
        rw [hj0]
        rfl
      rw [ha]
      have hnat : q + l - 1 - (e' ⟨j, k⟩ : ℕ) =
          (segs j).length - 1 - (k : ℕ) + l := by omega
      exact_mod_cast hnat
    · have hj1 : @Eq (Fin 2) j 1 := Fin.ext h1
      have hsj : (segs j).length = l := by rw [hj1]; exact hl₁
      simp only [h1, one_ne_zero, ↓reduceIte] at hv
      have ha : a j = 0 := by
        change ![(l : ℝ), 0] j = 0
        rw [hj1]
        rfl
      rw [ha, add_zero]
      have hnat : q + l - 1 - (e' ⟨j, k⟩ : ℕ) =
          (segs j).length - 1 - (k : ℕ) := by omega
      exact_mod_cast hnat
  have einner : ∀ j, Nonempty ((T.normalizedProductInductionFunctor.{uF, uV} (S j)).obj
        (fun k => (hsz ⟨j, k⟩).symm ▸ σ (e ⟨j, k⟩)) ≅
      T.segmentInducedDown (A' j).obj (segs j).length (segs j).rank_pos) := by
    intro j
    have hk : ∀ k, Nonempty (((hsz ⟨j, k⟩).symm ▸ σ (e ⟨j, k⟩) :
          SmoothRep.{0, uF, uV} ℂ (GeneralLinear ((S j).size k) F.Carrier)) ≅
        T.segmentFactorsDown (A' j).obj (segs j).length (segs j).rank_pos k) := fun k =>
      nonempty_cast_iso T A hA (a j) (hb j) (A' j) (hA' j) (hsz ⟨j, k⟩).symm (((segs j).length - 1 - (k : ℕ) : ℕ) : ℝ)
        (σ (e ⟨j, k⟩)) (eqToIso (congrArg (T.segmentFactor A.obj) (hexp ⟨j, k⟩)))
    exact ⟨(T.normalizedProductInductionFunctor (S j)).mapIso (Pi.isoMk fun k => (hk k).some)⟩
  obtain ⟨ε⟩ := regroup_nonempty_iso T B D S e hsz (index_index_eq_of_lt_iff B D S e hsz he) σ
    (fun j => T.segmentInducedDown (A' j).obj (segs j).length (segs j).rank_pos) einner
  let φ := SmoothRep.equivOfIso ε
  exact ⟨J.comp φ.toIntertwiningMap, hJ.comp φ.surjective⟩

/-- A selected actual surjective map from the full decreasing induction to the
product of the two supplied segment socles. -/
def decreasingUnionQuotient
    (hex : SegmentZelevinskyConstituentExistence.{uF,uV} F T) (ρ : CuspidalDatum.{uV, uF} T)
    (A : letI := T.topology; SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := ρ.rank))
    (hA : ρ.IsRepresentedBy A) (q l : ℕ)
    (d : T.SegmentProductDatum.{uV, uF} ((q + l) * ρ.rank)) (h₂ : d.length = 2)
    (hd : d.HasSegmentSocles)
    (hb₀ : (d.segments ⟨0, by omega⟩).base = ρ.twist l)
    (hl₀ : (d.segments ⟨0, by omega⟩).length = q)
    (hb₁ : (d.segments ⟨1, by omega⟩).base = ρ.twist 0)
    (hl₁ : (d.segments ⟨1, by omega⟩).length = l) :
    letI := T.topology
    {Q : (T.segmentInducedDown A.obj (q + l) ρ.rank_pos).representation.IntertwiningMap
      d.induced.representation // Function.Surjective Q} := by
  letI := T.topology
  have h := exists_surjective_from_decreasing T hex ρ A hA q l d h₂ hd hb₀ hl₀ hb₁ hl₁
  exact ⟨h.choose, h.choose_spec⟩

end Langlands.Classification.JuxtaposedShuffle
