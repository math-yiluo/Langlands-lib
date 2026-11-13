/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 226, 2026-11-13: extract M266.008 from commit
fbd320cd8b1b06487c58227e92eb135794267709; prefix the namespace with
Langlands.NYLL, prove the closed published Statement target, and replace
the source imports by the focused published target and additive proof.
The final equality uses definitional reduction rather than simp.
The retained license and notices are in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.UnramifiedNormSubgroup.MultiplicativeStatements
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.UnramifiedNormSubgroup.U003.Proofs

/-!
# Surjectivity of the multiplicative valuation modulo degree

Source: M266.008, lines 86–93 of
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/Existence/UnramifiedNormSubgroup.lean`.
-/

universe u

namespace Langlands.NYLL.LocalClassFieldTheory

/-- The multiplicative valuation-modulo-degree map is surjective. -/
theorem valuationModDegreeMulHom_surjective :
    valuationModDegreeMulHom_surjectiveStatement.{u} := by
  intro K _ _ _ _ n z
  rcases valuationModDegree_surjective K n (Multiplicative.toAdd z) with ⟨x, hx⟩
  refine ⟨Additive.toMul x, ?_⟩
  apply Multiplicative.toAdd.injective
  exact hx

end Langlands.NYLL.LocalClassFieldTheory
