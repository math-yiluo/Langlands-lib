import Langlands.Representation.Classification.JuxtaposedShuffleInducedIso
import Langlands.Representation.Classification.IrreducibleProductEmbedding
import Langlands.Representation.Classification.JuxtaposedRefinementTools

/-!
# The product of two segment socles inside one cuspidal induction

Let `ρ` be a cuspidal datum of rank `r` represented by `A`, and let `d` be a datum
with two segment socles `⟨Δ₀⟩, ⟨Δ₁⟩`, where `Δ₀` begins at `ν^l ρ` and has length
`q`, and `Δ₁` begins at `ρ` and has length `l`. Each socle embeds into the increasing
induction of its segment, normalized induction preserves injections, and the two
segment inductions regroup into one induction along the uniform shape `(r, …, r)`.
So `⟨Δ₀⟩ × ⟨Δ₁⟩` embeds into `i(ν^l A, …, ν^(l+q-1) A, A, …, ν^(l-1) A)`, the
product of the shuffle factors of the initial shuffle `{0, …, q-1}`.
-/

noncomputable section

namespace Langlands.Classification.JuxtaposedShuffle

open CategoryTheory GeneralLinear Geometric PadicField.TopologicalData Finset

universe uF uV

theorem shuffleExponent_initShuffle_of_lt {q l : ℕ} (a₀ a₁ : ℝ) (k : Fin (q + l))
    (hk : k.val < q) : shuffleExponent (initShuffle q l) a₀ a₁ k = a₀ + k.val := by
  unfold shuffleExponent
  rw [ite_eq_left (by simp [initShuffle, hk])]
  have h : (initShuffle q l).filter (· < k) =
      univ.filter (fun x : Fin (q + l) => x.val < k.val) := by
    ext x
    simp only [initShuffle, mem_filter, mem_univ, true_and, Fin.lt_def]
    omega
  rw [h, Fin.card_filter_val_lt, min_eq_right (by omega)]

theorem shuffleExponent_initShuffle_of_le {q l : ℕ} (a₀ a₁ : ℝ) (k : Fin (q + l))
    (hk : q ≤ k.val) :
    shuffleExponent (initShuffle q l) a₀ a₁ k = a₁ + ((k.val - q : ℕ) : ℝ) := by
  unfold shuffleExponent
  rw [ite_eq_right (by simp [initShuffle]; omega)]
  have h : (initShuffle q l)ᶜ.filter (· < k) =
      univ.filter (fun x : Fin (q + l) => x.val < k.val) \
        univ.filter (fun x : Fin (q + l) => x.val < q) := by
    ext x
    simp only [initShuffle, mem_filter, mem_compl, mem_univ, true_and, mem_sdiff, Fin.lt_def]
    omega
  rw [h, card_sdiff_of_subset (fun x => by simp only [mem_filter, mem_univ, true_and]; omega),
    Fin.card_filter_val_lt, Fin.card_filter_val_lt, min_eq_right (by omega),
    min_eq_right (by omega)]

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

/-- `⟨Δ₀⟩ × ⟨Δ₁⟩`, with `Δ₀` beginning at `ν^l ρ` of length `q` and `Δ₁` beginning at
`ρ` of length `l`, embeds into the induction along the uniform shape of the shuffle
factors of the initial shuffle `{0, …, q-1}`, that is of
`ν^l A, …, ν^(l+q-1) A, A, …, ν^(l-1) A`. -/
theorem exists_injective_initShuffle (ρ : CuspidalDatum.{uV, uF} T)
    (A : letI := T.topology; SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := ρ.rank))
    (hA : ρ.IsRepresentedBy A) (q l : ℕ)
    (d : T.SegmentProductDatum.{uV, uF} ((q + l) * ρ.rank)) (h₂ : d.length = 2)
    (hd : d.HasSegmentSocles)
    (hb₀ : (d.segments ⟨0, by omega⟩).base = ρ.twist l)
    (hl₀ : (d.segments ⟨0, by omega⟩).length = q)
    (hb₁ : (d.segments ⟨1, by omega⟩).base = ρ.twist 0)
    (hl₁ : (d.segments ⟨1, by omega⟩).length = l) :
    letI := T.topology
    ∃ i : d.induced.representation.IntertwiningMap
        ((T.normalizedProductInductionFunctor.{uF, uV}
          (BlockShape.uniform (q + l) ρ.rank ρ.rank_pos)).obj
            (shuffleFactors F T A.obj (q + l) ρ.rank_pos (initShuffle q l) l 0)).representation,
      Function.Injective i := by
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
  have hJ : ∀ j, ∃ J : (blocks j).representation.IntertwiningMap
      (T.segmentInduced (A' j).obj (segs j).length (segs j).rank_pos).representation,
      Function.Injective J := fun j => by
    obtain ⟨-, J, hJ, -⟩ := hsoc j
    exact ⟨J, hJ⟩
  choose J hJ using hJ
  obtain ⟨J₁, hJ₁⟩ := normalizedProduct_embedding_of_factor_embeddings F T
    (T.segmentShape segs hsum) blocks
    (fun j => T.segmentInduced (A' j).obj (segs j).length (segs j).rank_pos) J hJ
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
  let σ := shuffleFactors F T A.obj (q + l) ρ.rank_pos (initShuffle q l) l 0
  let e' : ((j : Fin D.length) × Fin (S j).length) ≃ Fin (q + l) :=
    finSigmaFinEquiv.trans (finCongr hlen)
  have hexp : ∀ x : (j : Fin D.length) × Fin (S j).length,
      shuffleExponent (initShuffle q l) (l : ℝ) 0 (e' x) = ((x.2 : ℕ) : ℝ) + a x.1 := by
    rintro ⟨j, k⟩
    have hk := k.isLt
    change (k : ℕ) < (segs j).length at hk
    have hv : ((e' ⟨j, k⟩ : Fin (q + l)) : ℕ) =
        (if j.val = 0 then 0 else (S (0 : Fin 2)).length) + k :=
      val_finSigmaFinEquiv_fin_two (n := fun j => (S j).length) ⟨j, k⟩
    have hS0 : (S (0 : Fin 2)).length = q := hl₀
    rw [hS0] at hv
    have hj : j.val < 2 := j.isLt
    change _ = ((k : ℕ) : ℝ) + a j
    rcases (show j.val = 0 ∨ j.val = 1 by omega) with h0 | h1
    · have hj0 : @Eq (Fin 2) j 0 := Fin.ext h0
      have hsj : (segs j).length = q := by rw [hj0]; exact hl₀
      simp only [h0, ↓reduceIte, zero_add] at hv
      have ha : a j = l := by
        change ![(l : ℝ), 0] j = l
        rw [hj0]
        rfl
      have h2 : (((e' ⟨j, k⟩ : Fin (q + l)) : ℕ) : ℝ) = ((k : ℕ) : ℝ) := by exact_mod_cast hv
      rw [shuffleExponent_initShuffle_of_lt (q := q) (l := l) (l : ℝ) 0 (e' ⟨j, k⟩) (by omega),
        h2, ha, add_comm]
    · have hj1 : @Eq (Fin 2) j 1 := Fin.ext h1
      simp only [h1, one_ne_zero, ↓reduceIte] at hv
      have ha : a j = 0 := by
        change ![(l : ℝ), 0] j = 0
        rw [hj1]
        rfl
      have h2 : ((((e' ⟨j, k⟩ : Fin (q + l)) : ℕ) - q : ℕ) : ℝ) = ((k : ℕ) : ℝ) := by
        rw [hv, Nat.add_sub_cancel_left]
      rw [shuffleExponent_initShuffle_of_le (q := q) (l := l) (l : ℝ) 0 (e' ⟨j, k⟩) (by omega),
        h2, ha, zero_add, add_zero]
  have einner : ∀ j, Nonempty ((T.normalizedProductInductionFunctor.{uF, uV} (S j)).obj
        (fun k => (hsz ⟨j, k⟩).symm ▸ σ (e ⟨j, k⟩)) ≅
      T.segmentInduced (A' j).obj (segs j).length (segs j).rank_pos) := by
    intro j
    have hk : ∀ k, Nonempty (((hsz ⟨j, k⟩).symm ▸ σ (e ⟨j, k⟩) :
          SmoothRep.{0, uF, uV} ℂ (GeneralLinear ((S j).size k) F.Carrier)) ≅
        T.segmentFactors (A' j).obj (segs j).length (segs j).rank_pos k) := fun k =>
      nonempty_cast_iso T A hA (a j) (hb j) (A' j) (hA' j) (hsz ⟨j, k⟩).symm ((k : ℕ) : ℝ)
        (σ (e ⟨j, k⟩)) (eqToIso (congrArg (T.segmentFactor A.obj) (hexp ⟨j, k⟩)))
    exact ⟨(T.normalizedProductInductionFunctor (S j)).mapIso (Pi.isoMk fun k => (hk k).some)⟩
  obtain ⟨ε⟩ := regroup_nonempty_iso T B D S e hsz (index_index_eq_of_lt_iff B D S e hsz he) σ
    (fun j => T.segmentInduced (A' j).obj (segs j).length (segs j).rank_pos) einner
  let φ := SmoothRep.equivOfIso ε.symm
  exact ⟨φ.toIntertwiningMap.comp J₁, φ.injective.comp hJ₁⟩

end Langlands.Classification.JuxtaposedShuffle
