import Langlands.Representation.Archimedean.RealInducedSwapGeneric
import Langlands.Representation.Archimedean.RealInductionStagesInduce

/-! # Composition and function inclusions for induction in stages -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean.InductionStages

open Langlands.LocalFactor.Archimedean
open RealBlockPosition RealBlockJacquet

variable {n a r : ℕ} {pre post ds es fs : List RealBlock}

/-- Replacing a slice with its position characters or otherwise dropping its
Fourier window conditions gives the corresponding ambient inclusion. -/
theorem kFin_le_inStages (hd : realRank ds = r) (he : realRank es = r)
    (hpos : realPositionCharacter es = realPositionCharacter ds)
    (hind : ∀ i d, realInducedBlockAt es i = some d → realInducedBlockAt ds i = some d) :
    KFin n (pre ++ ds ++ post) ≤ KFin n (pre ++ es ++ post) := by
  have hr : realRank es = realRank ds := he.trans hd.symm
  have hsplit (i : ℕ) :
      (i < realRank pre ∨ realRank pre + r ≤ i) ∨ ∃ j < r, i = realRank pre + j := by
    by_cases ho : i < realRank pre ∨ realRank pre + r ≤ i
    · exact Or.inl ho
    · exact Or.inr ⟨i - realRank pre, by omega, by omega⟩
  apply RealInducedSwapGeneric.kFin_le_of_conditions
  · funext i
    rcases hsplit i with ho | ⟨j, hj, rfl⟩
    · exact realPositionCharacter_of_not_mid hr (by simpa only [he] using ho)
    · rw [RealBlockPosition.realPositionCharacter_mid pre es post (he.symm ▸ hj),
        RealBlockPosition.realPositionCharacter_mid pre ds post (hd.symm ▸ hj), hpos]
  · intro i d hi
    rcases hsplit i with ho | ⟨j, hj, rfl⟩
    · rwa [← realInducedBlockAt_of_not_mid hr (by simpa only [he] using ho)]
    · rw [realInducedBlockAt_mid pre es post (he.symm ▸ hj)] at hi
      rw [realInducedBlockAt_mid pre ds post (hd.symm ▸ hj)]
      exact hind j d hi

/-- The slice of a function inclusion is the local function inclusion. -/
theorem sliceK_inclusion (h : a + r ≤ n) (ha : realRank pre = a)
    (hd : realRank ds = r) (he : realRank es = r)
    (hle : KFin r ds ≤ KFin r es)
    (hle' : KFin n (pre ++ ds ++ post) ≤ KFin n (pre ++ es ++ post))
    (κ : unitaryCompact ℝ n) (F : KFin n (pre ++ ds ++ post)) :
    sliceK h ha he κ (Submodule.inclusion hle' F) =
      Submodule.inclusion hle (sliceK h ha hd κ F) :=
  Subtype.ext rfl

theorem inclusion_map_kRep {m : ℕ} {xs ys : List RealBlock} (h : KFin m xs ≤ KFin m ys)
    (κ : unitaryCompact ℝ m) (f : KFin m xs) :
    Submodule.inclusion h (kRep m xs κ f) =
      kRep m ys κ (Submodule.inclusion h f) := by
  apply Subtype.ext
  change (kRep m xs κ f : Langlands.GeneralLinear m ℝ → ℂ) =
    (kRep m ys κ (Submodule.inclusion h f) : Langlands.GeneralLinear m ℝ → ℂ)
  rw [coe_kRep, coe_kRep]
  rfl

/-- Inducing a function inclusion gives the ambient function inclusion. -/
theorem ind_inclusion (h : a + r ≤ n) (ha : realRank pre = a)
    (hd : realRank ds = r) (he : realRank es = r) (hne : realRank (pre ++ es ++ post) = n)
    (hle : KFin r ds ≤ KFin r es)
    (hle' : KFin n (pre ++ ds ++ post) ≤ KFin n (pre ++ es ++ post)) :
    ind h ha he hd hne (Submodule.inclusion hle) (inclusion_map_kRep hle) =
      Submodule.inclusion hle' := by
  ext F : 1
  apply Subtype.ext
  refine eq_of_eqOn_unitaryCompact_of_mem_principalSeries
    (ind h ha he hd hne _ (inclusion_map_kRep hle) F).2.1.1
    (Submodule.inclusion hle' F).2.1.1 fun κ hκ => ?_
  rw [ind_apply_unitaryCompact h ha he hd hne (inclusion_map_kRep hle) F ⟨κ, hκ⟩]
  exact sliceK_apply_one h ha hd ⟨κ, hκ⟩ F

variable (h : a + r ≤ n) (ha : realRank pre = a) (hd : realRank ds = r)
  (he : realRank es = r) (hf : realRank fs = r)
  (hne : realRank (pre ++ es ++ post) = n) (hnf : realRank (pre ++ fs ++ post) = n)
  (T : KFin r ds →ₗ[ℂ] KFin r es) (S : KFin r es →ₗ[ℂ] KFin r fs)
  (hT : ∀ k v, T (kRep r ds k v) = kRep r es k (T v))
  (hS : ∀ k v, S (kRep r es k v) = kRep r fs k (S v))

include hT hS in
theorem comp_map_kRep (k : unitaryCompact ℝ r) (v : KFin r ds) :
    (S.comp T) (kRep r ds k v) = kRep r fs k ((S.comp T) v) := by
  simp only [LinearMap.comp_apply, hT, hS]

/-- The induced map of a composition equals the composition of the induced
maps. -/
def RealInductionStagesCompositionStatement : Prop :=
    ind h ha hf hd hnf (S.comp T) (comp_map_kRep T S hT hS) =
      (ind h ha hf he hnf S hS).comp (ind h ha he hd hne T hT)

theorem realInductionStagesComposition :
    RealInductionStagesCompositionStatement h ha hd he hf hne hnf T S hT hS := by
  ext F : 1
  apply Subtype.ext
  refine eq_of_eqOn_unitaryCompact_of_mem_principalSeries
    (ind h ha hf hd hnf _ (comp_map_kRep T S hT hS) F).2.1.1
    (ind h ha hf he hnf S hS (ind h ha he hd hne T hT F)).2.1.1 fun κ hκ => ?_
  change (ind h ha hf hd hnf _ (comp_map_kRep T S hT hS) F :
    Langlands.GeneralLinear n ℝ → ℂ) κ =
      (ind h ha hf he hnf S hS (ind h ha he hd hne T hT F) : Langlands.GeneralLinear n ℝ → ℂ) κ
  rw [ind_apply_unitaryCompact h ha hf hd hnf (comp_map_kRep T S hT hS) F ⟨κ, hκ⟩,
    ind_apply_unitaryCompact h ha hf he hnf hS (ind h ha he hd hne T hT F) ⟨κ, hκ⟩,
    sliceK_ind h ha he hd hne hT]
  rfl

end Langlands.Archimedean.InductionStages
