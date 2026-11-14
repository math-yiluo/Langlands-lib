/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteResidueFrobenius.U012.Proofs
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteResidueFrobenius.U017.Proofs
import Langlands.NYLL.GaloisCohomology.ProfiniteIntegers.ProfiniteIntegerCore.U022.Proofs

/-!
# M167.018: the profinite action and restriction (proof)
-/

namespace Langlands.NYLL.LocalClassFieldTheory

open ClassFormation

noncomputable section

universe u v w

variable (k : Type u) (L : Type v)
  [Field k] [Fintype k] [Field L] [Finite L] [Algebra k L]

section Tower

variable {E : Type v} {F : Type w}
  [Field E] [Finite E] [Field F] [Finite F]
  [Algebra k E] [Algebra k F] [Algebra E F]
  [IsScalarTower k E F] [Normal k E]

/-- The actions of `ℤ̂` on finite residue extensions commute with restriction
in finite towers. -/
theorem restrictNormalHom_finiteResidueFrobeniusFromZHat (z : ZHatMul) :
    restrictNormalHom_finiteResidueFrobeniusFromZHatStatement k (E := E) (F := F) z := by
  unfold restrictNormalHom_finiteResidueFrobeniusFromZHatStatement
  rw [finiteResidueFrobeniusFromZHat_apply,
    restrictNormalHom_finiteResidueFrobeniusExponentHom,
    finiteResidueFrobeniusFromZHat_apply]
  congr 2
  apply Multiplicative.ext
  exact zHatReduction_transition
    (m := Module.finrank k E) (n := Module.finrank k F)
    Module.finrank_pos Module.finrank_pos
    (show Module.finrank k E ∣ Module.finrank k F from
      ⟨Module.finrank E F,
        (Module.finrank_mul_finrank k E F).symm⟩)
    z.toAdd

end Tower

end
end Langlands.NYLL.LocalClassFieldTheory
