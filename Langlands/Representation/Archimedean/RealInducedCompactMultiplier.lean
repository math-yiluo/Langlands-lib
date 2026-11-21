import Langlands.Representation.Archimedean.RealInductionStagesInduce

/-! # Induced operators commute with invariant compact multipliers -/

noncomputable section

set_option autoImplicit false

namespace Langlands.Archimedean.InductionStages

open Langlands.LocalFactor.Archimedean

private theorem sliceK_compact_mul {n a r : ℕ} {pre ds post : List RealBlock}
    (h : a + r ≤ n) (ha : realRank pre = a) (hr : realRank ds = r)
    {φ : unitaryCompact ℝ n → ℂ}
    (hφ : ∀ l : unitaryCompact ℝ r, ∀ k, φ (blockEmbK h l * k) = φ k)
    {F f : KFin n (pre ++ ds ++ post)}
    (hF : ∀ k : unitaryCompact ℝ n, F.val k = φ k * f.val k)
    (k : unitaryCompact ℝ n) :
    sliceK h ha hr k F = φ k • sliceK h ha hr k f := by
  apply Subtype.ext
  refine eq_of_eqOn_unitaryCompact_of_mem_principalSeries
    (sliceK h ha hr k F).2.1.1 (φ k • sliceK h ha hr k f).2.1.1 fun l hl => ?_
  change slice h k F.val l = φ k * slice h k f.val l
  rw [slice_apply, slice_apply, sliceFactor_of_mem_unitaryCompact hl, one_mul, one_mul]
  have hlift := hF (blockEmbK h (⟨l, hl⟩ : unitaryCompact ℝ r) * k)
  rw [hφ, Subgroup.coe_mul, coe_blockEmbK] at hlift
  exact hlift

/-- The compact action of an induced block operator commutes with a multiplier
invariant under left multiplication by that block's compact group. -/
def RealInducedCompactMultiplierStatement : Prop :=
  ∀ {n a r : ℕ} {pre ds es post : List RealBlock}
    (h : a + r ≤ n) (ha : realRank pre = a) (hd : realRank ds = r)
    (he : realRank es = r) (hn : realRank (pre ++ es ++ post) = n)
    (T : KFin r ds →ₗ[ℂ] KFin r es)
    (hT : ∀ k f, T (kRep r ds k f) = kRep r es k (T f))
    (φ : unitaryCompact ℝ n → ℂ)
    (_ : ∀ l : unitaryCompact ℝ r, ∀ k, φ (blockEmbK h l * k) = φ k)
    (F f : KFin n (pre ++ ds ++ post)),
    (∀ k : unitaryCompact ℝ n, F.val k = φ k * f.val k) →
    ∀ k : unitaryCompact ℝ n,
      (ind h ha he hd hn T hT F).val k = φ k * (ind h ha he hd hn T hT f).val k

theorem realInducedCompactMultiplier : RealInducedCompactMultiplierStatement := by
  intro n a r pre ds es post h ha hd he hn T hT φ hφ F f hF k
  rw [ind_apply_unitaryCompact, ind_apply_unitaryCompact,
    sliceK_compact_mul h ha hd hφ hF, map_smul]
  rfl

end Langlands.Archimedean.InductionStages
