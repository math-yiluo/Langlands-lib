/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.GaloisStabilizer.Statements

/-!
# Finite-Galois stabilizer criterion: proof

Adapted from NYLL source unit M396.001 at commit
`fbd320cd8b1b06487c58227e92eb135794267709`.

Modifications by Worker 577: import the published proposition target, prefix
the source namespace with `Langlands.NYLL`, and prove that target with the
complete explicit field and instance telescope. The source fixed-field
argument is retained after introducing the target's quantified elements.
Attribution and license: `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

open scoped IntermediateField

universe u v

namespace Langlands.NYLL.RamificationTheory.HilbertRamification.Higher

/-- The exact finite-Galois stabilizer criterion, proved by fixed-field
correspondence with all parameters of the published target retained. -/
theorem adjoin_le_adjoin_of_forall_fixed_imp_fixed
    {K : Type u} {M : Type v}
    [Field K] [Field M] [Algebra K M]
    [FiniteDimensional K M] [IsGalois K M] :
    adjoin_le_adjoin_of_forall_fixed_imp_fixedStatement (K := K) (M := M) := by
  intro a b hfixed
  rw [← IsGalois.fixedField_fixingSubgroup K⟮b⟯,
    IntermediateField.adjoin_le_iff]
  intro x hx
  rw [Set.mem_singleton_iff] at hx
  subst x
  refine
    (IntermediateField.mem_fixedField_iff K⟮b⟯.fixingSubgroup a).2 ?_
  intro σ hσ
  exact hfixed σ
    (hσ ⟨b, IntermediateField.mem_adjoin_simple_self K b⟩)

end Langlands.NYLL.RamificationTheory.HilbertRamification.Higher
