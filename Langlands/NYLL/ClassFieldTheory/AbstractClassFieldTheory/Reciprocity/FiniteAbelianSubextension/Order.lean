/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteAbelianSubextension.Definitions

/-!
# NYLL M296.014: the field-inclusion order on finite abelian subextensions

Modified by Worker 448, 14 November 2026: extract the anonymous
`PartialOrder` instance M296.014 (source lines 144–155) from the pinned NYLL
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/FiniteAbelianSubextension.lean`
at `fbd320cd8b1b06487c58227e92eb135794267709`, prefix the namespace with
`Langlands.NYLL`, give the anonymous instance its reserved name
`Langlands.NYLL.PortInternal.M296.d014`, import only the published M296 data
module, and inline the source proof of `FiniteAbelianSubextension.ext`
(M296.013, lines 132–142) as a local `have` in the antisymmetry field, since
that theorem is not yet proved in the Library. The paired Markdown records
every modification. See `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

noncomputable section

namespace Langlands.NYLL.ClassFormation

universe u

section GroupOnly

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace FiniteAbelianSubextension

variable {K : ClosedSubgroup G}

/-- The order is field inclusion.  Since fields are represented by their
absolute Galois subgroups, it is the opposite subgroup order. -/
instance _root_.Langlands.NYLL.PortInternal.M296.d014 :
    PartialOrder (FiniteAbelianSubextension K) where
  le L₁ L₂ := L₂.field.toSubgroup ≤ L₁.field.toSubgroup
  le_refl _ := le_rfl
  le_trans _ _ _ h₁₂ h₂₃ := h₂₃.trans h₁₂
  le_antisymm L₁ L₂ h₁₂ h₂₁ := by
    -- The source proof of `FiniteAbelianSubextension.ext` (M296.013, source
    -- lines 132–142), unchanged, as a local lemma.
    have ext : ∀ {L₁ L₂ : FiniteAbelianSubextension K},
        L₁.field = L₂.field → L₁ = L₂ := by
      intro L₁ L₂ h
      cases L₁ with
      | mk L₁ h₁ =>
          cases L₂ with
          | mk L₂ h₂ =>
              cases L₁ with
              | mk F₁ b₁ n₁ f₁ =>
                  cases L₂ with
                  | mk F₂ b₂ n₂ f₂ =>
                      dsimp only [field] at h
                      cases h
                      rfl
    apply ext
    apply ClosedSubgroup.ext
    have hs : L₁.field.toSubgroup = L₂.field.toSubgroup :=
      le_antisymm h₂₁ h₁₂
    exact congrArg (fun H : Subgroup G => H.carrier) hs

end FiniteAbelianSubextension

end GroupOnly

end Langlands.NYLL.ClassFormation
