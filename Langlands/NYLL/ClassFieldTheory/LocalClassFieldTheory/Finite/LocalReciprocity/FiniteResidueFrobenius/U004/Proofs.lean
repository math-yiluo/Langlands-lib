/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteResidueFrobenius.Statements

/-!
# M167.004: integer exponents (proof)
-/

namespace Langlands.NYLL.LocalClassFieldTheory

open ClassFormation

noncomputable section

universe u v w

variable (k : Type u) (L : Type v)
  [Field k] [Fintype k] [Field L] [Finite L] [Algebra k L]


/-- An integer residue exponent maps to the corresponding power of Frobenius. -/
@[simp]
theorem finiteResidueFrobeniusExponentHom_intCast (m : ℤ) :
    finiteResidueFrobeniusExponentHom_intCastStatement k L m := by
  unfold finiteResidueFrobeniusExponentHom_intCastStatement finiteResidueFrobeniusExponentHom
  exact congrArg Additive.toMul (ZMod.lift_coe _ _ m)

end
end Langlands.NYLL.LocalClassFieldTheory
