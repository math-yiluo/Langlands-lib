/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteResidueFrobenius.Statements

/-!
# M167.016: Frobenius and restriction (proof)
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

/-- Arithmetic Frobenius commutes with restriction in a tower of finite
extensions of a finite field. -/
theorem restrictNormalHom_finiteResidueFrobenius :
    restrictNormalHom_finiteResidueFrobeniusStatement k (E := E) (F := F) := by
  apply AlgEquiv.ext
  intro x
  apply (algebraMap E F).injective
  calc
    (algebraMap E F)
        (((AlgEquiv.restrictNormalHom E)
          (FiniteField.frobeniusAlgEquivOfAlgebraic k F)) x) =
        FiniteField.frobeniusAlgEquivOfAlgebraic k F
          (algebraMap E F x) :=
      AlgEquiv.restrictNormal_commutes
        (FiniteField.frobeniusAlgEquivOfAlgebraic k F) E x
    _ = (algebraMap E F
        ((FiniteField.frobeniusAlgEquivOfAlgebraic k E) x) : F) := by
      simp only [FiniteField.coe_frobeniusAlgEquivOfAlgebraic]
      exact (map_pow (algebraMap E F) x (Fintype.card k)).symm

end Tower

end
end Langlands.NYLL.LocalClassFieldTheory
