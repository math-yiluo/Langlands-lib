/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.SetTheory.Cardinal.Finite
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteResidueFrobenius.U006.Proofs

/-!
# M167.007: injectivity (proof)
-/

namespace Langlands.NYLL.LocalClassFieldTheory

open ClassFormation

noncomputable section

universe u v w

variable (k : Type u) (L : Type v)
  [Field k] [Fintype k] [Field L] [Finite L] [Algebra k L]


/-- The finite-level Frobenius exponent homomorphism is injective. -/
theorem finiteResidueFrobeniusExponentHom_injective :
    finiteResidueFrobeniusExponentHom_injectiveStatement k L := by
  let : NeZero (Module.finrank k L) := ⟨Module.finrank_pos.ne'⟩
  have hcard :
      Nat.card (Multiplicative (ZMod (Module.finrank k L))) =
        Nat.card (L ≃ₐ[k] L) := by
    rw [Nat.card_congr Multiplicative.toAdd,
      Nat.card_zmod, IsGalois.card_aut_eq_finrank]
  exact ((finiteResidueFrobeniusExponentHom_surjective k L).bijective_of_nat_card_le
    hcard.le).1

end
end Langlands.NYLL.LocalClassFieldTheory
