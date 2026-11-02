import Langlands.Representation.Classification.JuxtaposedUniqueProperSub
import Langlands.Representation.Classification.JuxtaposedUnionSeparation
import Langlands.Representation.Classification.JuxtaposedSwapFromLibrary
import Langlands.Representation.Classification.LinkedSegmentSocleReverseProductStepsStatement
import Langlands.Representation.Filtration.LengthTwoMatching
import Langlands.Representation.Classification.JuxtaposedUnionHead
import Langlands.Representation.CuspidalSupport.NonassociatedJacquetSubquotientsProof
import Langlands.Representation.Classification.SegmentZelevinskyConstituentExistenceProof
import Langlands.Representation.Classification.SegmentFullJacquetProof

/-!
# Conditional assembly of the juxtaposed case of Zelevinsky's Proposition 4.6

This file derives `JuxtaposedSegmentSocleReverseProductStructure` from explicit
hypotheses: the shuffle count of `TwoSegmentSocleShuffleJacquet`, the vanishing of
quasicuspidal Jacquet subquotients along nonassociated Levis, Zelevinsky's formula
3.1 for the Jacquet module of a segment socle, the irreducibility of the products
`ν^a A × ν^b A` of two supercuspidal twists with `b + 1 < a`, and the union datum
with its head (part H). The last theorem discharges the nonassociated vanishing,
formula 3.1 and part H by published proofs, leaving the shuffle count and the
two-factor irreducibility as hypotheses.
-/

noncomputable section

set_option linter.style.haveILetI false

open Representation CategoryTheory

namespace Langlands.Classification.JuxtaposedShuffle

open GeneralLinear PadicField.TopologicalData CuspidalSupport CuspidalSupport.JacquetLength
open LengthCriterionProof (quotientRep)

universe uF uV uW

/-- A sum over `Fin m` with `m = 2` has two terms. -/
theorem sum_fin_eq_two {m : ℕ} (h : m = 2) (f : Fin m → ℕ) :
    ∑ i, f i = f ⟨0, by omega⟩ + f ⟨1, by omega⟩ := by
  subst h
  rw [Fin.sum_univ_two]
  rfl

section Subrepresentations

open LengthCriterionProof (lower)

variable {k : Type*} [Field k] {G : Type*} [Monoid G] {V : Type*} [AddCommGroup V]
  [Module k V] {ρ : Representation k G V}

/-- The successive quotient `K / ⊥` is the representation on `K`. -/
def quotientRepBotEquiv (K : Subrepresentation ρ) :
    (quotientRep (⊥ : Subrepresentation ρ) K).Equiv K.toRepresentation :=
  .mk (Submodule.quotEquivOfEqBot (lower (⊥ : Subrepresentation ρ) K)
      (eq_bot_iff.2 fun x hx => (Submodule.mem_bot k).2
        (Subtype.ext ((LengthTwo.mem_bot_iff (ρ := ρ) (x : V)).1 hx))))
    fun g => LinearMap.ext fun y => by
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      rfl

/-- The top invariant subspace carries the whole representation. -/
def topSubrepresentationEquiv (ρ : Representation k G V) :
    (⊤ : Subrepresentation ρ).toRepresentation.Equiv ρ :=
  .mk { toFun := fun x => (x : V)
        invFun := fun v => ⟨v, LengthTwo.mem_top v⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    fun _ => LinearMap.ext fun _ => rfl

/-- An irreducible invariant subspace is nonzero. -/
theorem subrepresentation_ne_bot_of_isIrreducible {K : Subrepresentation ρ}
    (hK : IsIrreducible K.toRepresentation) : K ≠ ⊥ := by
  rintro rfl
  refine hK.bot_ne_top (le_antisymm bot_le fun v _ => ?_)
  exact (LengthTwo.mem_bot_iff v).2 (Subtype.ext ((LengthTwo.mem_bot_iff (ρ := ρ) (v : V)).1 v.2))

/-- An invariant subspace contained in an irreducible invariant subspace `K` is zero or
`K`. -/
theorem eq_bot_or_eq_of_le_isIrreducible {K L : Subrepresentation ρ}
    (hK : IsIrreducible K.toRepresentation) (hLK : L ≤ K) : L = ⊥ ∨ L = K := by
  let ι : K.toRepresentation.IntertwiningMap ρ :=
    { toLinearMap := K.toSubmodule.subtype
      isIntertwining' := fun _ => rfl }
  rcases hK.eq_bot_or_eq_top (LengthTwo.comap ι L) with h | h
  · refine Or.inl (le_antisymm (fun v hv => ?_) bot_le)
    have hmem : (⟨v, hLK hv⟩ : K.toSubmodule) ∈ LengthTwo.comap ι L := hv
    rw [h, LengthTwo.mem_bot_iff] at hmem
    exact (LengthTwo.mem_bot_iff v).2 (congrArg Subtype.val hmem)
  · refine Or.inr (le_antisymm hLK fun v hv => ?_)
    have hmem : (⟨v, hv⟩ : K.toSubmodule) ∈ LengthTwo.comap ι L := h ▸ LengthTwo.mem_top _
    exact hmem

end Subrepresentations

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

/-- Under the shuffle count, `⟨Δ₀⟩ × ⟨Δ₁⟩` is nonzero: its Jacquet module has a
composition series of positive length. -/
theorem bot_ne_top_induced
    (hS1 : TwoSegmentSocleShuffleJacquet.{uF, uV, max uF uV} F T)
    (ρ : CuspidalDatum.{uV, uF} T)
    (A : letI := T.topology; SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := ρ.rank))
    (hA : ρ.IsRepresentedBy A) (q l : ℕ)
    (d : T.SegmentProductDatum.{uV, uF} ((q + l) * ρ.rank)) (h₂ : d.length = 2)
    (hd : d.HasSegmentSocles)
    (hb₀ : (d.segments ⟨0, by omega⟩).base = ρ.twist l)
    (hl₀ : (d.segments ⟨0, by omega⟩).length = q)
    (hb₁ : (d.segments ⟨1, by omega⟩).base = ρ.twist 0)
    (hl₁ : (d.segments ⟨1, by omega⟩).length = l) :
    letI := T.topology
    (⊥ : Subrepresentation d.induced.representation) ≠ ⊤ := by
  letI := T.topology
  intro h
  let C := BlockShape.uniform (q + l) ρ.rank ρ.rank_pos
  have hq : 0 < q := hl₀ ▸ (d.segments ⟨0, by omega⟩).length_pos
  obtain ⟨s, hs⟩ := (hS1 ρ A (l : ℝ) 0 q l d h₂ hA hd hb₀ hl₀ hb₁ hl₁).1
  have hN : 0 < (q + l).choose q := Nat.choose_pos (by omega)
  have hcov := (LengthCriterionProof.hasSimpleFactors_iff_covBy s).1 hs ⟨0, hN⟩
  have hJ : ∀ S : Subrepresentation
      (CuspidalJacquetMultiplicity.upperJacquet T C d.induced.obj).ρ, S = ⊥ := by
    intro S
    refine le_antisymm (fun x _ => ?_) bot_le
    obtain ⟨v, rfl⟩ := C.jacquetMk_surjective d.induced.representation x
    have hv : v = 0 := (LengthTwo.mem_bot_iff v).1 (h ▸ LengthTwo.mem_top v)
    subst hv
    exact (LengthTwo.mem_bot_iff _).2 (map_zero _)
  exact hcov.lt.ne ((hJ _).trans (hJ _).symm)

/-- **Core assembly.** Under the hypotheses of the counting argument, let `σ` be a
representation of `GL_((q+l) r)` whose Jacquet module is the identity shuffle
tensor, and assume every irreducible quotient of `π = ⟨Δ₀⟩ × ⟨Δ₁⟩` is equivalent
to `σ`. Then `π` has a two-step filtration with simple factors, graded piece 1
equivalent to `σ`, graded piece 0 not equivalent to `σ`, and every irreducible
subrepresentation of `π` equal to its middle step. -/
theorem exists_filtration_core
    (hS1 : TwoSegmentSocleShuffleJacquet.{uF, uV, max uF uV} F T)
    (ρ : CuspidalDatum.{uV, uF} T)
    (A : letI := T.topology; SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := ρ.rank))
    (hA : ρ.IsRepresentedBy A) (q l : ℕ) (hq : 0 < q) (hl : 0 < l)
    (hnon : NonassociatedJacquetSubquotientsTheorem.{uF, uV} F T ((q + l) * ρ.rank))
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
    (hhead : letI := T.topology
      ∀ K : Subrepresentation d.induced.representation,
        IsIrreducible (quotientRep K ⊤) → Nonempty ((quotientRep K ⊤).Equiv σ)) :
    letI := T.topology
    ∃ s : ObjectRepFiltration (Rep.of d.induced.representation) 2,
      s.HasSimpleFactors ∧ Nonempty ((s.gradedRepresentation 1).ρ.Equiv σ) ∧
        ¬ Nonempty ((s.gradedRepresentation 0).ρ.Equiv σ) ∧
        ∀ K : Subrepresentation d.induced.representation,
          IsIrreducible K.toRepresentation → K = s.subrepresentation 1 := by
  letI := T.topology
  have huniq : ∀ X Y : Subrepresentation d.induced.representation,
      X ≠ ⊥ → X ≠ ⊤ → Y ≠ ⊥ → Y ≠ ⊤ → X = Y := fun X Y hX₀ hX₁ hY₀ hY₁ =>
    eq_of_ne_bot_of_ne_top_induced T hS1 ρ A hA q l hnon d h₂ hd hb₀ hl₀ hb₁ hl₁ hswap
      X Y hX₀ hX₁ hY₀ hY₁
  have hsep : ∀ X : Subrepresentation d.induced.representation, X ≠ ⊥ →
      ¬ Nonempty (X.toRepresentation.Equiv σ) := fun X hX =>
    not_nonempty_equiv_of_ne_bot T ρ A hA q l hq hl d h₂ hd hb₀ hl₀ hb₁ hl₁ hswap σ hσ X hX
  have hbt := bot_ne_top_induced T hS1 ρ A hA q l d h₂ hd hb₀ hl₀ hb₁ hl₁
  obtain ⟨K, hK₀, hK₁⟩ : ∃ K : Subrepresentation d.induced.representation,
      K ≠ ⊥ ∧ K ≠ ⊤ := by
    by_contra hno
    have hπ : IsIrreducible d.induced.representation :=
      { toNontrivial := ⟨⟨⊥, ⊤, hbt⟩⟩
        eq_bot_or_eq_top := fun K => by
          by_cases h : K = ⊥
          · exact Or.inl h
          · exact Or.inr (by_contra fun h' => hno ⟨K, h, h'⟩) }
    let e₁ := quotientRepBotEquiv (⊤ : Subrepresentation d.induced.representation)
    let e₀ := e₁.trans (topSubrepresentationEquiv d.induced.representation)
    obtain ⟨E⟩ := hhead ⊥ (LengthTwo.isIrreducible_of_equiv e₀.symm hπ)
    exact hsep ⊤ hbt.symm ⟨e₁.symm.trans E⟩
  have hcov₀ : ⊥ ⋖ K := ⟨bot_lt_iff_ne_bot.2 hK₀, fun X hX₁ hX₂ =>
    hX₂.ne (huniq X K hX₁.ne' (hX₂.trans_le le_top).ne hK₀ hK₁)⟩
  have hcov₁ : K ⋖ ⊤ := ⟨lt_top_iff_ne_top.2 hK₁, fun X hX₁ hX₂ =>
    hX₁.ne' (huniq X K (bot_le.trans_lt hX₁).ne' hX₂.ne hK₀ hK₁)⟩
  refine ⟨LengthTwo.twoStep K, LengthTwo.twoStep_hasSimpleFactors hcov₀ hcov₁, ?_, ?_, ?_⟩
  · exact hhead K (LengthTwo.isIrreducible_gradedRep_of_covBy hcov₁)
  · rintro ⟨E⟩
    exact hsep K hK₀ ⟨(quotientRepBotEquiv K).symm.trans E⟩
  · intro K' hK'
    have h₀ := subrepresentation_ne_bot_of_isIrreducible hK'
    have h₁ : K' ≠ ⊤ := by
      rintro rfl
      rcases eq_bot_or_eq_of_le_isIrreducible hK' (le_top : K ≤ ⊤) with h | h
      · exact hK₀ h
      · exact hK₁ h
    exact huniq K' K h₀ h₁ hK₀ hK₁

/-- **Conditional juxtaposed case of Zelevinsky 1980, Proposition 4.6.** The target
proposition follows from the explicit hypotheses `hS1` (shuffle count), `hnon`
(nonassociated Jacquet subquotients), `hfull` (Zelevinsky 3.1), `hirr` (the
irreducibility of `ν^a A × ν^b A` for `b + 1 < a`) and `hH` (the union datum and the
head of `⟨Δ⟩ × ⟨Δ'⟩`). -/
theorem juxtaposedSegmentSocleReverseProductStructure_of_inputs
    (hS1 : TwoSegmentSocleShuffleJacquet.{uF, uV, max uF uV} F T)
    (hnon : ∀ n, NonassociatedJacquetSubquotientsTheorem.{uF, uV} F T n)
    (hfull : SegmentSubrepresentationFullJacquet.{uF, uV} F T)
    (hirr : ∀ {r : ℕ} (hr : 0 < r)
      (A : letI := T.topology; SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := r))
      (a b : ℕ), b + 1 < a → letI := T.topology
        ((T.normalizedProductInductionFunctor.{uF, uV} (BlockShape.uniform 2 r hr)).obj
          ![T.segmentFactor A.obj (a : ℝ), T.segmentFactor A.obj (b : ℝ)]).IsIrreducible)
    (hH : letI := T.topology
      ∀ (n : ℕ) (d : T.SegmentProductDatum.{uV, uF} n) (h₂ : d.length = 2),
        d.HasSegmentSocles →
        (d.segments ⟨1, by omega⟩).Precedes (d.segments ⟨0, by omega⟩) →
        (d.segments ⟨1, by omega⟩).IsJuxtaposed (d.segments ⟨0, by omega⟩) →
        (d.segments ⟨0, by omega⟩).base =
            (d.segments ⟨1, by omega⟩).base.twist ((d.segments ⟨1, by omega⟩).length : ℝ) ∧
          ∃ (U : T.Segment.{uV, uF}) (I : Option (T.Segment.{uV, uF}))
            (e : T.SegmentProductDatum.{uV, uF} n),
            (d.segments ⟨0, by omega⟩).IsUnionIntersectionReplacement
                (d.segments ⟨1, by omega⟩) U I ∧
              List.ofFn e.segments = U :: I.toList ∧
              e.HasSegmentSocles ∧
              Representation.IsIrreducible e.induced.representation ∧
              e.length = 1 ∧
              (∀ i, (e.segments i).base = (d.segments ⟨1, by omega⟩).base ∧
                (e.segments i).length =
                  (d.segments ⟨0, by omega⟩).length + (d.segments ⟨1, by omega⟩).length) ∧
              ∀ K : Subrepresentation d.induced.representation,
                IsIrreducible (quotientRep K ⊤) →
                  Nonempty ((quotientRep K ⊤).Equiv e.induced.representation)) :
    JuxtaposedSegmentSocleReverseProductStructure.{uF, uV} F T := by
  intro n d h₂ hd hprec hjux
  letI := T.topology
  obtain ⟨hbase, U, I, e, hrep, hlist, hes, hirre, he₁, hesegs, hhead⟩ :=
    hH n d h₂ hd hprec hjux
  refine ⟨U, I, e, hrep, hlist, hes, hirre, ?_⟩
  have key : ∀ (ρ : CuspidalDatum.{uV, uF} T)
      (A : SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := ρ.rank)),
      ρ.IsRepresentedBy A → (d.segments ⟨1, by omega⟩).base = ρ →
      ∃ s : ObjectRepFiltration (Rep.of d.induced.representation) 2,
        s.HasSimpleFactors ∧
          Nonempty ((s.gradedRepresentation 1).ρ.Equiv e.induced.representation) ∧
          ¬ Nonempty ((s.gradedRepresentation 0).ρ.Equiv e.induced.representation) ∧
          ∀ K : Subrepresentation d.induced.representation,
            Representation.IsIrreducible K.toRepresentation → K = s.subrepresentation 1 := by
    intro ρ A hA hρ
    obtain ⟨q, hq⟩ : ∃ q, (d.segments ⟨0, by omega⟩).length = q := ⟨_, rfl⟩
    obtain ⟨l, hl⟩ : ∃ l, (d.segments ⟨1, by omega⟩).length = l := ⟨_, rfl⟩
    rw [hρ, hl] at hbase
    have hn : n = (q + l) * ρ.rank := by
      rw [← d.degree_sum, sum_fin_eq_two h₂ (fun i => (d.segments i).degree), add_mul]
      change (d.segments ⟨0, by omega⟩).length * (d.segments ⟨0, by omega⟩).base.rank +
        (d.segments ⟨1, by omega⟩).length * (d.segments ⟨1, by omega⟩).base.rank = _
      rw [hbase, hρ, hq, hl]
      rfl
    subst hn
    have hq₀ : 0 < q := hq ▸ (d.segments ⟨0, by omega⟩).length_pos
    have hl₀ : 0 < l := hl ▸ (d.segments ⟨1, by omega⟩).length_pos
    have hb₁ : (d.segments ⟨1, by omega⟩).base = ρ.twist 0 := by
      rw [hρ, CuspidalDatum.twist_zero]
    have hswap := segmentFactor_swap_of_isIrreducible' ρ.rank_pos A
      (hirr ρ.rank_pos A)
    have hσ := nonempty_jacquet_single_equiv T hfull ρ A hA (q + l) e he₁ hes
      ((hesegs _).1.trans hρ) ((hesegs _).2.trans (by rw [hq, hl]))
    rw [← shuffleFactors_idShuffle T ρ.rank_pos A.obj q l] at hσ
    exact exists_filtration_core T hS1 ρ A hA q l hq₀ hl₀ (hnon _) d h₂ hd hbase hq hb₁ hl
      hswap e.induced.representation hσ hhead
  obtain ⟨A, hA, -⟩ := hd ⟨1, by omega⟩
  exact key _ A hA rfl

/-- The conditional assembly with `hnon` discharged by the published
`CuspidalSupport.nonassociatedJacquetSubquotients`, `hfull` by the first clause of the
published `segmentFullJacquetFormula` (Zelevinsky 3.1), and part H by
`exists_juxtaposedUnionHead` applied to the published
`segmentZelevinskyConstituentExistence`. -/
theorem juxtaposedSegmentSocleReverseProductStructure_of_irreducible
    (hS1 : TwoSegmentSocleShuffleJacquet.{uF, uV, max uF uV} F T)
    (hirr : ∀ {r : ℕ} (hr : 0 < r)
      (A : letI := T.topology; SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := r))
      (a b : ℕ), b + 1 < a → letI := T.topology
        ((T.normalizedProductInductionFunctor.{uF, uV} (BlockShape.uniform 2 r hr)).obj
          ![T.segmentFactor A.obj (a : ℝ), T.segmentFactor A.obj (b : ℝ)]).IsIrreducible) :
    JuxtaposedSegmentSocleReverseProductStructure.{uF, uV} F T :=
  juxtaposedSegmentSocleReverseProductStructure_of_inputs T hS1
    (fun n => CuspidalSupport.nonassociatedJacquetSubquotients F T n)
    (segmentFullJacquetFormula F T).1 hirr
    fun _ d h₂ hd hp hj => exists_juxtaposedUnionHead T
      (segmentZelevinskyConstituentExistence F T) d h₂ hd hp hj

end Langlands.Classification.JuxtaposedShuffle
