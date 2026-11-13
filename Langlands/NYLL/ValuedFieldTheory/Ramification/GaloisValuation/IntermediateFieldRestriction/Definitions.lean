/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Adapted by Worker 30, 13 November 2026: moved RamificationTheory.intermediateFieldRestrictNormalHom
to Langlands.NYLL.RamificationTheory.intermediateFieldRestrictNormalHom and split
out this single definition (inventory M259.001). The import, universes, section
variables, telescope, return type and tactic body are unchanged.
The retained license and notice are licenses/NYLL/LICENSE and licenses/NYLL/NOTICE.
-/

import Mathlib.FieldTheory.Galois.Basic

/-!
# Restriction between normal intermediate fields

Source: Naganori Yamaguchi, ClassFieldTheory, commit
fbd320cd8b1b06487c58227e92eb135794267709,
`Nyll/ValuedFieldTheory/Ramification/GaloisValuation/IntermediateFieldRestriction.lean`,
lines 21–36 (inventory M259.001).
-/

noncomputable section

namespace Langlands.NYLL.RamificationTheory

universe u v

variable {K : Type u} {Omega : Type v}
  [Field K] [Field Omega] [Algebra K Omega]

/-- Restriction `Gal(F/K) → Gal(E/K)` for two intermediate fields `E ≤ F`
in one ambient extension. -/
noncomputable def intermediateFieldRestrictNormalHom
    (E F : IntermediateField K Omega) (hEF : E ≤ F) [Normal K E] :
    (F ≃ₐ[K] F) →* (E ≃ₐ[K] E) := by
  letI : Algebra E F :=
    RingHom.toAlgebra (IntermediateField.inclusion hEF).toRingHom
  letI : IsScalarTower K E F := IsScalarTower.of_algebraMap_eq' rfl
  exact AlgEquiv.restrictNormalHom E

end Langlands.NYLL.RamificationTheory
