/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 3, 2026-11-13: prove the published closed target of M264.010,
the theorem galoisGroupResidueAlgEquivOfIsIntegralClosure_arithmeticFrobenius_apply
at lines 175–190 of upstream commit fbd320cd8b1b06487c58227e92eb135794267709,
under the same name prefixed with Langlands.NYLL. The proof inlines the source
lemmas M264.002, M264.008, M264.009 and M161.037 instead of citing them. The
source imports are replaced by the published target module. The retained license
and notices are in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.UnramifiedFrobenius.ResidueActionStatement

/-!
# Residue action of the field arithmetic Frobenius: proof

This module proves the published closed target for NYLL M264.010.
-/

namespace Langlands.NYLL.LocalFieldTheory

universe u

open scoped ValuativeRel

/-- The field arithmetic Frobenius of a finite Galois unramified extension of
nonarchimedean local fields acts on residues by `x ↦ x ^ #𝓀[K]`. This proves the
closed target for NYLL M264.010. -/
theorem galoisGroupResidueAlgEquivOfIsIntegralClosure_arithmeticFrobenius_apply :
    galoisGroupResidueAlgEquivOfIsIntegralClosure_arithmeticFrobenius_applyStatement.{u} := by
  intro K L _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ x
  -- The forward map of the isomorphism is the residue action, so the residue
  -- action of the inverse image of residue Frobenius is residue Frobenius.
  have hfrob :
      galoisGroupResidueAlgEquivOfIsIntegralClosure K L
          (arithmeticFrobeniusOfUnramifiedValuation K L) =
        residueExtensionArithmeticFrobeniusOfValuationExtension K L :=
    (galoisGroupEquivResidueAlgEquivOfUnramifiedValuationOfIsIntegralClosure K L).apply_symm_apply
      (residueExtensionArithmeticFrobeniusOfValuationExtension K L)
  rw [hfrob]
  -- Residue Frobenius is Mathlib's finite-field Frobenius `x ↦ x ^ #𝓀[K]`.
  let := Fintype.ofFinite 𝓀[K]
  change FiniteField.frobeniusAlgEquivOfAlgebraic 𝓀[K] 𝓀[L] x = x ^ Nat.card 𝓀[K]
  simp [Nat.card_eq_fintype_card]

end Langlands.NYLL.LocalFieldTheory
