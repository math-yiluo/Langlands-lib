/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteResidueFrobenius.U005.Proofs
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteResidueFrobenius.U012.Proofs

/-!
# M167.013: the profinite exponent one (proof)
-/

namespace Langlands.NYLL.LocalClassFieldTheory

open ClassFormation

noncomputable section

universe u v w

variable (k : Type u) (L : Type v)
  [Field k] [Fintype k] [Field L] [Finite L] [Algebra k L]


/-- The distinguished profinite integer `1` acts as arithmetic Frobenius. -/
@[simp]
theorem finiteResidueFrobeniusFromZHat_one :
    finiteResidueFrobeniusFromZHat_oneStatement k L := by
  show finiteResidueFrobeniusFromZHat k L _ = _
  rw [finiteResidueFrobeniusFromZHat_apply]
  exact finiteResidueFrobeniusExponentHom_one k L

end
end Langlands.NYLL.LocalClassFieldTheory
