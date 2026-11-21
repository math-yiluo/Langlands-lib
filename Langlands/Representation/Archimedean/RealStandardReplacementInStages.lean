import Langlands.Representation.Archimedean.RealCompactIteratedFourier
import Langlands.Representation.Archimedean.RealInducedFourierMultiplier
import Langlands.Representation.Archimedean.RealStandardEquivStages

/-! # Right-split Fourier replacements under induction in stages -/

noncomputable section

open scoped Matrix.Norms.Operator TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean.InductionStages

attribute [local instance 100] LieRing.ofAssociativeRing

open Langlands.LocalFactor.Archimedean RealInducedBlockBound RealInducedTorusCore RealTemperedForm

/-- A forward Fourier multiplier with a compact-equivariant right inverse.
The forward map also intertwines the real Lie action. -/
structure SplitFourierReplacement (n : ℕ) (ds es : List RealBlock) where
  forward : KFin n ds →ₗ[ℂ] KFin n es
  reverse : KFin n es →ₗ[ℂ] KFin n ds
  slots : List (Slot n)
  weights : List ℤ → ℕ
  split : ∀ f, forward (reverse f) = f
  reverse_compact : ∀ (k : Matrix.unitaryGroup (Fin n) ℝ) f,
    reverse (realStandardRep n es k f) = realStandardRep n ds k (reverse f)
  forward_lie : ∀ (X : Matrix (Fin n) (Fin n) ℝ) f,
    forward (realStandardLie n ds (1 ⊗ₜ X) f) = realStandardLie n es (1 ⊗ₜ X) (forward f)
  disjoint : slots.Pairwise Slot.Disjoint
  coefficient : ∀ J : List ℤ, J.length = slots.length → ∀ f k, k ∈ unitaryCompact ℝ n →
    coeffs (withModes slots J) (forward f).val k =
      (weights J : ℂ) * coeffs (withModes slots J) f.val k

namespace SplitFourierReplacement

variable {n : ℕ} {ds es fs : List RealBlock}

/-- The replacement of each nonzero-weight induced block by its two
characters admits a split Fourier replacement. -/
theorem nonempty_characterReplacement (h : realRank ds = n) :
    Nonempty (SplitFourierReplacement n (ds.flatMap repl) ds) := by
  have hChain : ChainData n 0 (ds.flatMap repl) ds := by
    simpa using chain (n := n) ds [] (by simpa using h)
  obtain ⟨T, S, L, W, hTS, hSK, hTL, hL, -, hW⟩ := hChain
  exact ⟨⟨T, S, L, W, hTS, hSK, hTL, hL, hW⟩⟩

theorem forward_compact (R : SplitFourierReplacement n ds es) :
    ∀ k f, R.forward (kRep n ds k f) = kRep n es k (R.forward f) :=
  compactEquivariant_of_iteratedFourierMultiplier R.slots (fun J => (R.weights J : ℂ))
    R.forward R.coefficient

theorem reverse_kRep (R : SplitFourierReplacement n ds es) :
    ∀ k f, R.reverse (kRep n es k f) = kRep n ds k (R.reverse f) := by
  intro k f
  exact R.reverse_compact (toUnitary n k) f

theorem forward_intertwiner (R : SplitFourierReplacement n ds es) :
    IsRealStandardIntertwiner n (realStandardRep n es) (realStandardLie n es) ds R.forward :=
  isRealStandardIntertwiner_iff.mpr ⟨R.forward_compact, R.forward_lie⟩

private theorem disjoint_shiftSlots {a r : ℕ} (h : a + r ≤ n) {L : List (Slot r)}
    (hL : L.Pairwise Slot.Disjoint) : (L.map (shiftSlot h)).Pairwise Slot.Disjoint := by
  rw [List.pairwise_map]
  refine hL.imp fun {t u} htu => ?_
  change (a + t.p) + 1 < a + u.p ∨ (a + u.p) + 1 < a + t.p
  rcases htu with ht | hu
  · left; omega
  · right; omega

/-- The split replacement extends to a surrounding standard module with the
same rotations shifted to the middle block. -/
def inStages {a r : ℕ} {pre xs ys post : List RealBlock}
    (R : SplitFourierReplacement r xs ys)
    (h : a + r ≤ n) (ha : realRank pre = a)
    (hx : realRank xs = r) (hy : realRank ys = r)
    (hnx : realRank (pre ++ xs ++ post) = n) (hny : realRank (pre ++ ys ++ post) = n) :
    SplitFourierReplacement n (pre ++ xs ++ post) (pre ++ ys ++ post) where
  forward := ind h ha hy hx hny R.forward R.forward_compact
  reverse := ind h ha hx hy hnx R.reverse R.reverse_kRep
  slots := R.slots.map (shiftSlot h)
  weights := R.weights
  split f := by
    let F := ind h ha hy hx hny R.forward R.forward_compact
    let S := ind h ha hx hy hnx R.reverse R.reverse_kRep
    change F (S f) = f
    apply Subtype.ext
    refine eq_of_eqOn_unitaryCompact_of_mem_principalSeries (F (S f)).2.1.1 f.2.1.1
      fun k hk => ?_
    let κ : unitaryCompact ℝ n := ⟨k, hk⟩
    change (F (S f)).val κ = f.val κ
    rw [ind_apply_unitaryCompact, sliceK_ind, R.split, sliceK_apply_one]
  reverse_compact k f := by
    simpa only [kRep, toUnitary_ofUnitary] using
      ind_kRep h ha hx hy hnx R.reverse_kRep (ofUnitary n k) f
  forward_lie X f := by
    exact (standardInd_intertwiner h ha hy hx hny R.forward_intertwiner).map_realStandardLie
      (1 ⊗ₜ X) f
  disjoint := disjoint_shiftSlots h R.disjoint
  coefficient J hJ f k hk := by
    have hLength : J.length = R.slots.length := by simpa using hJ
    exact realInducedFourierMultiplier h ha hx hy hny R.forward R.forward_compact
      R.slots (fun J => (R.weights J : ℂ)) R.coefficient J hLength f k hk

/-- Composing replacements supported in disjoint slots multiplies their
weights and composes the right inverses in reverse order. -/
def compDisjoint (R : SplitFourierReplacement n ds es) (S : SplitFourierReplacement n es fs)
    (h : ∀ t ∈ R.slots, ∀ u ∈ S.slots, t.Disjoint u) : SplitFourierReplacement n ds fs where
  forward := S.forward.comp R.forward
  reverse := R.reverse.comp S.reverse
  slots := R.slots ++ S.slots
  weights J := R.weights (J.take R.slots.length) * S.weights (J.drop R.slots.length)
  split f := by simp only [LinearMap.comp_apply, R.split, S.split]
  reverse_compact k f := by
    simp only [LinearMap.comp_apply, S.reverse_compact, R.reverse_compact]
  forward_lie X f := by simp only [LinearMap.comp_apply, R.forward_lie, S.forward_lie]
  disjoint := List.pairwise_append.mpr ⟨R.disjoint, S.disjoint, h⟩
  coefficient J hJ f k hk := by
    simp only [LinearMap.comp_apply, Nat.cast_mul]
    exact iteratedFourierMultiplier_comp_of_disjoint R.slots S.slots
      (fun J => (R.weights J : ℂ)) (fun J => (S.weights J : ℂ)) h R.forward S.forward
      R.coefficient S.coefficient J hJ f k hk

end SplitFourierReplacement

/-- The construction supplies an ambient split Fourier replacement for any
middle replacement with the specified rank data. -/
def RealStandardReplacementInStagesStatement : Prop :=
  ∀ {n a r : ℕ} {pre xs ys post : List RealBlock}
    (R : SplitFourierReplacement r xs ys)
    (h : a + r ≤ n) (ha : realRank pre = a)
    (hx : realRank xs = r) (hy : realRank ys = r)
    (hnx : realRank (pre ++ xs ++ post) = n) (hny : realRank (pre ++ ys ++ post) = n),
    ∃ S : SplitFourierReplacement n (pre ++ xs ++ post) (pre ++ ys ++ post),
      S.forward = ind h ha hy hx hny R.forward R.forward_compact ∧
      S.reverse = ind h ha hx hy hnx R.reverse R.reverse_kRep

theorem realStandardReplacementInStages : RealStandardReplacementInStagesStatement := by
  intro n a r pre xs ys post R h ha hx hy hnx hny
  exact ⟨R.inStages h ha hx hy hnx hny, rfl, rfl⟩

end Langlands.Archimedean.InductionStages
