import Langlands.Representation.Classification.JuxtaposedJacquetCover
import Langlands.Representation.Classification.JuxtaposedShuffleDistinct
import Langlands.Representation.Classification.SegmentFullJacquetStatement
import Langlands.Representation.Induction.SingleBlock
import Langlands.Representation.CuspidalSupport.CuspidalTensorProof

/-!
# No nonzero subrepresentation of `⟨Δ₀⟩ × ⟨Δ₁⟩` is equivalent to `⟨Δ₁ ∪ Δ₀⟩`

Let `Δ₀` begin at `ν^l ρ` with length `q`, let `Δ₁` begin at `ρ` with length `l`, and
let `J` be the normalized Jacquet functor along the uniform shape `(r, …, r)`.
Every nonzero subrepresentation `X` of `⟨Δ₀⟩ × ⟨Δ₁⟩` has a nonzero map from `J(X)`
to the initial shuffle tensor `τ_{S₀}`. A representation whose Jacquet module is the
identity shuffle tensor `τ_{S_id}`, for instance the socle of the union segment
(Zelevinsky 1980, 3.1, a hypothesis here), is therefore not equivalent to `X`.
-/

noncomputable section

set_option linter.style.haveILetI false

open Representation CategoryTheory

namespace Langlands.Classification.JuxtaposedShuffle

open GeneralLinear PadicField.TopologicalData CuspidalSupport CuspidalSupport.JacquetLength
open Finset

universe uF uV uW

/-- The identity shuffle carries the increasing exponents `0, 1, …, q + l - 1`. -/
theorem shuffleExponent_idShuffle (q l : ℕ) (i : Fin (q + l)) :
    shuffleExponent (idShuffle q l) (l : ℝ) 0 i = ((i : ℕ) : ℝ) := by
  have hlt : (univ.filter (fun j : Fin (q + l) => j < i)).card = i := by
    have h : univ.filter (fun j : Fin (q + l) => j < i) = Iio i := by
      ext j
      simp
    rw [h, Fin.card_Iio]
  unfold shuffleExponent
  by_cases h : l ≤ i.val
  · have hi : i ∈ idShuffle q l := by simp [idShuffle, h]
    rw [ite_eq_left hi]
    have hsplit := Finset.card_filter_add_card_filter_not
      (s := univ.filter (fun j : Fin (q + l) => j < i)) (fun j => j ∈ idShuffle q l)
    have hc : (univ.filter (fun j : Fin (q + l) => j < i)).filter (fun j => j ∉ idShuffle q l) =
        Iio (⟨l, by omega⟩ : Fin (q + l)) := by
      ext j
      simp only [idShuffle, mem_filter, mem_univ, true_and, mem_Iio, Fin.lt_def, not_le]
      omega
    have hs : (univ.filter (fun j : Fin (q + l) => j < i)).filter (fun j => j ∈ idShuffle q l) =
        (idShuffle q l).filter (· < i) := by
      ext j
      simp only [mem_filter, mem_univ, true_and]
      tauto
    rw [hc, hs, hlt, Fin.card_Iio] at hsplit
    have hcard : ((idShuffle q l).filter (· < i)).card = i.val - l := by
      simp only at hsplit
      omega
    rw [hcard, Nat.cast_sub h]
    ring
  · have hi : i ∉ idShuffle q l := by simp [idShuffle]; omega
    rw [ite_eq_right hi, zero_add]
    have hc : (idShuffle q l)ᶜ.filter (· < i) = univ.filter (fun j : Fin (q + l) => j < i) := by
      ext j
      simp only [idShuffle, mem_filter, mem_compl, mem_univ, true_and, Fin.lt_def, not_le]
      omega
    rw [hc, hlt]

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

/-- The identity shuffle tensor is the increasing segment tensor
`A ⊗ νA ⊗ … ⊗ ν^(q+l-1) A`. -/
theorem shuffleFactors_idShuffle {r : ℕ} (hr : 0 < r)
    (A : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear r F.Carrier)) (q l : ℕ) :
    shuffleFactors F T A (q + l) hr (idShuffle q l) l 0 = T.segmentFactors A (q + l) hr := by
  funext i
  exact congrArg (T.segmentFactor A) (shuffleExponent_idShuffle q l i)

/-- **Jacquet module of a one-segment socle datum.** Assume Zelevinsky's formula 3.1
for the full Jacquet module of a segment subrepresentation. If `e` has the single
segment with beginning `ρ` and length `m`, and its block is a socle of that
segment, then the normalized Jacquet module of `e.induced` along the uniform shape
is equivalent to `A ⊗ νA ⊗ … ⊗ ν^(m-1) A`. -/
theorem nonempty_jacquet_single_equiv
    (hfull : SegmentSubrepresentationFullJacquet.{uF, uV} F T)
    (ρ : CuspidalDatum.{uV, uF} T)
    (A : letI := T.topology; SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := ρ.rank))
    (hA : ρ.IsRepresentedBy A) (m : ℕ)
    (e : T.SegmentProductDatum.{uV, uF} (m * ρ.rank)) (h₁ : e.length = 1)
    (he : e.HasSegmentSocles)
    (hb : (e.segments ⟨0, by omega⟩).base = ρ)
    (hl : (e.segments ⟨0, by omega⟩).length = m) :
    letI := T.topology
    Nonempty ((T.normalizedJacquet (BlockShape.uniform m ρ.rank ρ.rank_pos)
        e.induced.representation).Equiv
      (FiniteTensor.externalSmoothObject (T.segmentFactors A.obj m ρ.rank_pos)).representation) := by
  letI := T.topology
  obtain ⟨len, segs, hsum, blocks⟩ := e
  dsimp only at h₁ hb hl
  have h0 : 0 < len := by rw [h₁]; exact Nat.one_pos
  have hb' : (segs ⟨0, h0⟩).base = ρ := hb
  have hl' : (segs ⟨0, h0⟩).length = m := hl
  clear hb hl
  subst hb'
  subst hl'
  let i0 : Fin len := ⟨0, h0⟩
  let Δ := segs i0
  let B := T.segmentShape segs hsum
  let τ := fun i => (blocks i).representation
  have hB : B.length = 1 := h₁
  let E := T.singleBlockNormalizedProductEquiv B hB τ (fun i => (blocks i).isSmooth) i0
  have hτ : (τ i0).comp (GeneralLinear.reindex (R := F.Carrier)
      (finCongr (B.singleBlock_size hB i0))).symm.toMonoidHom = (blocks i0).representation := by
    have hg : ∀ g, (GeneralLinear.reindex (R := F.Carrier)
        (finCongr (B.singleBlock_size hB i0))).symm g = g := by
      intro g
      apply Units.ext
      ext a b
      rfl
    ext g : 1
    exact congrArg (τ i0) (hg g)
  have hsub : T.IsSegmentSubrepresentation Δ (blocks i0) := by
    obtain ⟨A', hA', hsoc⟩ := he i0
    exact ⟨A', hA', hsoc.1, hsoc.2.choose, hsoc.2.choose_spec.1⟩
  obtain ⟨F'⟩ := hfull Δ A (blocks i0) hA hsub
  refine ⟨(normalizedJacquetEquiv T (BlockShape.uniform Δ.length Δ.base.rank Δ.base.rank_pos)
    (E.trans (equivOfRepresentationEq hτ))).trans F'⟩

/-- **Separation from the union.** Let `σ` be a representation of `GL_((q+l) r)` whose
normalized Jacquet module along the uniform shape is equivalent to the identity
shuffle tensor. Assume the two-block swaps of `hswap`. Then no nonzero
subrepresentation of `⟨Δ₀⟩ × ⟨Δ₁⟩` is equivalent to `σ`. -/
theorem not_nonempty_equiv_of_ne_bot
    (ρ : CuspidalDatum.{uV, uF} T)
    (A : letI := T.topology; SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := ρ.rank))
    (hA : ρ.IsRepresentedBy A) (q l : ℕ) (hq : 0 < q) (hl : 0 < l)
    (d : T.SegmentProductDatum.{uV, uF} ((q + l) * ρ.rank)) (h₂ : d.length = 2)
    (hd : d.HasSegmentSocles)
    (hb₀ : (d.segments ⟨0, by omega⟩).base = ρ.twist l)
    (hl₀ : (d.segments ⟨0, by omega⟩).length = q)
    (hb₁ : (d.segments ⟨1, by omega⟩).base = ρ.twist 0)
    (hl₁ : (d.segments ⟨1, by omega⟩).length = l)
    (hswap : ∀ a b : ℕ, b + 1 < a → letI := T.topology
      Nonempty ((T.normalizedProductInductionFunctor.{uF, uV}
          (BlockShape.uniform 2 ρ.rank ρ.rank_pos)).obj
            ![T.segmentFactor A.obj (a : ℝ), T.segmentFactor A.obj (b : ℝ)] ≅
        (T.normalizedProductInductionFunctor.{uF, uV}
          (BlockShape.uniform 2 ρ.rank ρ.rank_pos)).obj
            ![T.segmentFactor A.obj (b : ℝ), T.segmentFactor A.obj (a : ℝ)]))
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (σ : Representation ℂ (GeneralLinear ((q + l) * ρ.rank) F.Carrier) W)
    (hσ : letI := T.topology
      Nonempty ((T.normalizedJacquet (BlockShape.uniform (q + l) ρ.rank ρ.rank_pos) σ).Equiv
        (FiniteTensor.externalSmoothObject
          (shuffleFactors F T A.obj (q + l) ρ.rank_pos (idShuffle q l) l 0)).representation))
    (X : letI := T.topology; Subrepresentation d.induced.representation) (hX : X ≠ ⊥) :
    ¬ Nonempty (X.toRepresentation.Equiv σ) := by
  letI := T.topology
  rintro ⟨E⟩
  obtain ⟨Eσ⟩ := hσ
  let C := BlockShape.uniform (q + l) ρ.rank ρ.rank_pos
  obtain ⟨g, hg⟩ := exists_ne_zero_jacquet_hom_shuffle T ρ A hA q l d h₂ hd hb₀ hl₀ hb₁ hl₁
    hswap (initShuffle q l) (card_initShuffle q l) (initShuffle_ne_idShuffle hq hl) X hX
  let JE := normalizedJacquetEquiv T C E
  let f := g.comp (JE.symm.toIntertwiningMap.comp Eσ.symm.toIntertwiningMap)
  have hf : f ≠ 0 := by
    intro h
    apply hg
    refine DFunLike.ext _ _ fun x => ?_
    have hx := DFunLike.congr_fun h (Eσ (JE x))
    change g (JE.symm (Eσ.symm (Eσ (JE x)))) = 0 at hx
    rw [Representation.Equiv.symm_apply_apply, Representation.Equiv.symm_apply_apply] at hx
    exact hx
  have hirr : ∀ S : Finset (Fin (q + l)), IsIrreducible (FiniteTensor.externalSmoothObject
      (shuffleFactors F T A.obj (q + l) ρ.rank_pos S l 0)).representation := fun S =>
    (glCuspidalTensor p F T ((q + l) * ρ.rank) (Nat.mul_pos (by omega) ρ.rank_pos) C
      (fun k => segmentSupercuspidalFactor F T A (shuffleExponent (m := q + l) S (l : ℝ) 0 k))).1
  haveI := hirr (idShuffle q l)
  haveI := hirr (initShuffle q l)
  have hbij := (IsIrreducible.bijective_or_eq_zero f).resolve_right hf
  exact initShuffle_ne_idShuffle hq hl (eq_of_shuffleTensor_equiv T ρ.rank_pos A
    (card_initShuffle q l) (card_idShuffle q l) (IntertwiningMap.ofBijective f hbij).symm)

end Langlands.Classification.JuxtaposedShuffle
