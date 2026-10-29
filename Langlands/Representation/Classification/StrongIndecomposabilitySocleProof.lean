import Langlands.Representation.Classification.StrongIndecomposabilitySocleStatement
import Langlands.Representation.Classification.StrongConstituentExtremaProof

noncomputable section

namespace Langlands.Classification

open scoped MonoidAlgebra

universe uK uG uH uV

variable {k : Type uK} [Field k] {G : Type uG} [Group G]
  {V : Type uV} [AddCommGroup V] [Module k V] {ρ : Representation k G V}

theorem unique_atom_of_stronglyIndecomposable [Nontrivial V]
    (hArt : IsArtinian k[G] ρ.asModule) (h : IsStronglyIndecomposable ρ) :
    ∃! S : Subrepresentation ρ, IsAtom S := by
  let := hArt
  let : Nontrivial ρ.asModule := by
    change Nontrivial V
    infer_instance
  let e := Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := ρ)
  obtain ⟨N, hN⟩ := IsAtomic.exists_atom
    (α := Submodule k[G] ρ.asModule)
  let S := e.symm N
  have hS : IsAtom S := (e.symm.isAtom_iff N).mpr hN
  refine ⟨S, hS, ?_⟩
  intro T hT
  have hST := h S T hS.ne_bot hT.ne_bot
  exact ((hT.ne_bot_iff_eq inf_le_right).mp hST).symm.trans
    ((hS.ne_bot_iff_eq inf_le_left).mp hST)

theorem stronglyIndecomposable_of_unique_atom
    (hArt : IsArtinian k[G] ρ.asModule)
    (h : ∃! S : Subrepresentation ρ, IsAtom S) :
    IsStronglyIndecomposable ρ := by
  let := hArt
  let e := Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := ρ)
  let : IsAtomic (Subrepresentation ρ) := e.isAtomic_iff.mpr inferInstance
  obtain ⟨A, hA, huniq⟩ := h
  intro S T hS hT
  obtain ⟨B, hB, hBS⟩ := (eq_bot_or_exists_atom_le S).resolve_left hS
  obtain ⟨C, hC, hCT⟩ := (eq_bot_or_exists_atom_le T).resolve_left hT
  rw [huniq B hB] at hBS
  rw [huniq C hC] at hCT
  intro hST
  exact hA.ne_bot (le_bot_iff.mp (hST ▸ le_inf hBS hCT))

theorem stronglyIndecomposable_of_comp {H : Type uH} [Group H]
    (f : H →* G) (h : IsStronglyIndecomposable (ρ.comp f)) :
    IsStronglyIndecomposable ρ := by
  let r (S : Subrepresentation ρ) : Subrepresentation (ρ.comp f) :=
    { toSubmodule := S.toSubmodule
      apply_mem_toSubmodule := fun g _ hv => S.apply_mem_toSubmodule (f g) hv }
  have hr (S : Subrepresentation ρ) (hS : S ≠ ⊥) : r S ≠ ⊥ := by
    intro hbot
    exact hS (Subrepresentation.toSubmodule_injective
      (congrArg (fun U : Subrepresentation (ρ.comp f) => U.toSubmodule) hbot))
  intro S T hS hT hST
  exact h (r S) (r T) (hr S hS) (hr T hT)
    (Subrepresentation.toSubmodule_injective
      (congrArg (fun U : Subrepresentation ρ => U.toSubmodule) hST))

theorem strongIndecomposabilitySocle :
    StrongIndecomposabilitySocleStatement.{uK, uG, uH, uV} := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k _ G _ V _ _ _ ρ hArt
    exact ⟨unique_atom_of_stronglyIndecomposable hArt,
      stronglyIndecomposable_of_unique_atom hArt⟩
  · intro G _ V _ _ _ ρ hArt h
    exact (strongConstituentExtrema G V ρ).2.mp
      (unique_atom_of_stronglyIndecomposable hArt h)
  · intro G _ _ A hnonzero hArt h
    let := hnonzero
    refine ⟨A.socleSubrepresentation, ?_⟩
    exact (strongConstituentExtrema G A A.representation).2.mp
      (unique_atom_of_stronglyIndecomposable hArt h)
  · intro k _ G _ H _ V _ _ ρ f h
    exact stronglyIndecomposable_of_comp f h

end Langlands.Classification
