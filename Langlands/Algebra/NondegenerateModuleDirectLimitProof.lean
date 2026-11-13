import Langlands.Algebra.IdempotentedRingDirectLimitProof
import Mathlib.Algebra.Module.CharacterModule

set_option autoImplicit false

noncomputable section

namespace Langlands.Algebra

universe uA uM uT

open IdempotentedDirectLimitProof

/-- Renard I.1.2: cofinal idempotents detect nondegeneracy and give the direct limit. -/
theorem nondegenerateModuleDirectLimitStatement :
    NondegenerateModuleDirectLimitStatement.{uA, uM, uT} := by
  intro A _ hA M _ _ J hJ
  have hfixed : IsNondegenerate A M ↔ ∀ m : M, ∃ e ∈ J, (e : A) • m = m := by
    constructor
    · intro h m
      obtain ⟨e, he⟩ := h m
      obtain ⟨f, hf, hef⟩ := hJ {e}
      exact ⟨f, hf, Idempotent.smul_eq_of_le (hef e (Finset.mem_singleton_self e)) he⟩
    · intro h m
      obtain ⟨e, _, he⟩ := h m
      exact ⟨e, he⟩
  refine ⟨hfixed, ?_⟩
  constructor
  · intro h T _ g hg
    obtain ⟨H, hH, hU⟩ := additiveUnion
      (fun e : J => e.val.leftImage M)
      (fun _ _ hef _ hm => Idempotent.smul_eq_of_le hef hm)
      (directed J hJ)
      (fun m => by
        obtain ⟨e, he, hm⟩ := hfixed.mp h m
        exact ⟨⟨e, he⟩, hm⟩)
      (fun e => g e.val e.property)
      (fun e f hef => hg e.val e.property f.val f.property hef)
    exact ⟨H, fun e he => hH ⟨e, he⟩,
      fun H' hH' => hU H' (fun e => hH' e.val e.property)⟩
  · intro hlim m
    let S : AddSubgroup M := (nondegeneratePart hA M).toAddSubgroup
    let q : M →+ M ⧸ S := QuotientAddGroup.mk' S
    have hq : q m = 0 := by
      apply CharacterModule.eq_zero_of_character_apply
      intro c
      let H : M →+ ULift.{uT} (AddCircle (1 : ℚ)) :=
        AddEquiv.ulift.symm.toAddMonoidHom.comp (c.comp q)
      obtain ⟨F, _, hU⟩ := hlim (ULift.{uT} (AddCircle (1 : ℚ)))
        (fun _ _ => 0) (by intros; rfl)
      have hH : ∀ e (he : e ∈ J) (n : e.leftImage M), H n = 0 := by
        intro e _ n
        have hn : (n : M) ∈ S := ⟨e, n.property⟩
        have hqn : q n = 0 := (QuotientAddGroup.eq_zero_iff _).mpr hn
        change ULift.up (c (q n)) = 0
        rw [hqn, map_zero]
        rfl
      have hzero : H = 0 := (hU H hH).trans (hU 0 (by intro e he n; rfl)).symm
      exact congrArg ULift.down (DFunLike.congr_fun hzero m)
    exact (QuotientAddGroup.eq_zero_iff m).mp hq

end Langlands.Algebra
