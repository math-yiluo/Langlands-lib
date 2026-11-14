/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteResidueFrobenius.U004.Proofs

/-!
# M167.005: exponent one (proof)
-/

namespace Langlands.NYLL.LocalClassFieldTheory

open ClassFormation

noncomputable section

universe u v w

variable (k : Type u) (L : Type v)
  [Field k] [Fintype k] [Field L] [Finite L] [Algebra k L]


/-- Residue exponent one maps to the arithmetic Frobenius automorphism. -/
@[simp]
theorem finiteResidueFrobeniusExponentHom_one :
    finiteResidueFrobeniusExponentHom_oneStatement k L := by
  have h := finiteResidueFrobeniusExponentHom_intCast k L 1
  unfold finiteResidueFrobeniusExponentHom_intCastStatement at h
  simpa using h

end
end Langlands.NYLL.LocalClassFieldTheory
