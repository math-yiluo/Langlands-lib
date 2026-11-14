/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteResidueFrobenius.U004.Proofs

/-!
# M167.006: surjectivity (proof)
-/

namespace Langlands.NYLL.LocalClassFieldTheory

open ClassFormation

noncomputable section

universe u v w

variable (k : Type u) (L : Type v)
  [Field k] [Fintype k] [Field L] [Finite L] [Algebra k L]


/-- Every finite residue-field automorphism is a power of arithmetic
Frobenius, so the canonical exponent homomorphism is onto. -/
theorem finiteResidueFrobeniusExponentHom_surjective :
    finiteResidueFrobeniusExponentHom_surjectiveStatement k L := by
  intro sigma
  obtain ⟨m, hm⟩ :=
    (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow k L).2 sigma
  refine ⟨Multiplicative.ofAdd
    ((m.1 : ℤ) : ZMod (Module.finrank k L)), ?_⟩
  rw [finiteResidueFrobeniusExponentHom_intCast]
  simpa [zpow_natCast] using hm

end
end Langlands.NYLL.LocalClassFieldTheory
