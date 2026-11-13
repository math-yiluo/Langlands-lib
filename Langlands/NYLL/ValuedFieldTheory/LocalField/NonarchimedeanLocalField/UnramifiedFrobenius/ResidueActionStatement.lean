/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 3, 2026-11-13: state only M264.010, the theorem
galoisGroupResidueAlgEquivOfIsIntegralClosure_arithmeticFrobenius_apply at
lines 175–190 of upstream commit fbd320cd8b1b06487c58227e92eb135794267709, as a
closed proposition named with the suffix `Statement` in the namespace prefixed
with Langlands.NYLL; omit the source proof; replace the source imports by the
published module defining the field arithmetic Frobenius. The retained license
and notices are in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.UnramifiedFrobenius.FieldDefinitions

/-!
# Residue action of the field arithmetic Frobenius: target

This module states only M264.010, lines 175–190 of
`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/UnramifiedFrobenius.lean`.
-/

namespace Langlands.NYLL.LocalFieldTheory

universe u

open scoped ValuativeRel

/-- Target for NYLL M264.010: the field arithmetic Frobenius of a finite Galois
unramified extension of nonarchimedean local fields acts on residues by
`x ↦ x ^ #𝓀[K]`. -/
def galoisGroupResidueAlgEquivOfIsIntegralClosure_arithmeticFrobenius_applyStatement :
    Prop :=
  ∀ (K L : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L]
    [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] [Module.Finite 𝒪[K] 𝒪[L]]
    [IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (x : 𝓀[L]),
    galoisGroupResidueAlgEquivOfIsIntegralClosure K L
        (arithmeticFrobeniusOfUnramifiedValuation K L) x =
      x ^ Nat.card 𝓀[K]

end Langlands.NYLL.LocalFieldTheory
