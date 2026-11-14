/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 3, 2026-11-13: prove M264.016, the theorem
isCyclic_galoisGroup_of_unramifiedValuation at lines 400–412 of
Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/UnramifiedFrobenius.lean
at upstream commit fbd320cd8b1b06487c58227e92eb135794267709, typed as the
published isCyclic_galoisGroup_of_unramifiedValuationStatement in the namespace
prefixed with Langlands.NYLL. The source proof goes through the arithmetic
Frobenius generator (M264.006, M264.014, M264.015); this proof instead
transports Mathlib's cyclicity of the Galois group of a finite field along the
published isomorphism M161.036. The retained license and notices are in
licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.UnramifiedFrobenius.CyclicStatement
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteUnramified.ResidueEquivDefinitions

/-!
# The Galois group of a finite unramified extension is cyclic: proof

Proof of NYLL M264.016.
-/

namespace Langlands.NYLL.LocalFieldTheory

universe u

/-- The Galois group of a finite unramified extension is cyclic. -/
theorem isCyclic_galoisGroup_of_unramifiedValuation :
    isCyclic_galoisGroup_of_unramifiedValuationStatement.{u} := by
  intro K L _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  exact (galoisGroupEquivResidueAlgEquivOfUnramifiedValuationOfIsIntegralClosure K L).isCyclic.mpr
    inferInstance

end Langlands.NYLL.LocalFieldTheory
