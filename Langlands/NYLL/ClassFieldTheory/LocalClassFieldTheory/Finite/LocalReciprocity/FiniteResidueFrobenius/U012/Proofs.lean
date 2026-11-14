/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteResidueFrobenius.Statements

/-!
# M167.012: profinite action through reduction (proof)
-/

namespace Langlands.NYLL.LocalClassFieldTheory

open ClassFormation

noncomputable section

universe u v w

variable (k : Type u) (L : Type v)
  [Field k] [Fintype k] [Field L] [Finite L] [Algebra k L]


/-- The profinite Frobenius map depends on reduction modulo the residue extension degree. -/
@[simp]
theorem finiteResidueFrobeniusFromZHat_apply (z : ZHatMul) :
    finiteResidueFrobeniusFromZHat_applyStatement k L z :=
  rfl

end
end Langlands.NYLL.LocalClassFieldTheory
