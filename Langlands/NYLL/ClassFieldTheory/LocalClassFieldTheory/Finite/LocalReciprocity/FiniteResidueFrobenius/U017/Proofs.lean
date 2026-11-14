/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteResidueFrobenius.U004.Proofs
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteResidueFrobenius.U016.Proofs

/-!
# M167.017: exponent coordinates and restriction (proof)
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

/-- The finite Frobenius exponent coordinates commute with restriction. -/
theorem restrictNormalHom_finiteResidueFrobeniusExponentHom
    (z : Multiplicative (ZMod (Module.finrank k F))) :
    restrictNormalHom_finiteResidueFrobeniusExponentHomStatement k (E := E) z := by
  unfold restrictNormalHom_finiteResidueFrobeniusExponentHomStatement
  rcases ZMod.intCast_surjective z.toAdd with ⟨m, hm⟩
  have hz : z = Multiplicative.ofAdd
      (m : ZMod (Module.finrank k F)) := by
    apply Multiplicative.ext
    exact hm.symm
  subst z
  apply AlgEquiv.ext
  intro x
  rw [finiteResidueFrobeniusExponentHom_intCast]
  simp only [toAdd_ofAdd]
  have hred :
      ZMod.castHom
          (show Module.finrank k E ∣ Module.finrank k F from
            ⟨Module.finrank E F,
              (Module.finrank_mul_finrank k E F).symm⟩)
          (ZMod (Module.finrank k E))
          (m : ZMod (Module.finrank k F)) =
        (m : ZMod (Module.finrank k E)) := by
    exact map_intCast _ m
  rw [hred, finiteResidueFrobeniusExponentHom_intCast]
  have hfrob := restrictNormalHom_finiteResidueFrobenius
    (k := k) (E := E) (F := F)
  have hpow := congrArg (fun sigma : E ≃ₐ[k] E => sigma ^ m) hfrob
  rw [map_zpow]
  exact DFunLike.congr_fun hpow x

end Tower

end
end Langlands.NYLL.LocalClassFieldTheory
