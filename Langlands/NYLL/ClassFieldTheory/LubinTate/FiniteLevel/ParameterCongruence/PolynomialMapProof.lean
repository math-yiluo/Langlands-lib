/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 660, 2026-11-16: extract only the proof of M392.001
(lines 43–50) at upstream commit fbd320cd8b1b06487c58227e92eb135794267709;
prefix the namespace with Langlands.NYLL and prove the existing closed
Prop target with independent universes, importing its published module.
The retained license and notices are in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.ParameterCongruence.PolynomialMapStatement

/-!
# Equal-parameter polynomial map proof

This module proves the published target extracted from M392.001 of
`Nyll/ClassFieldTheory/LubinTate/FiniteLevel/ParameterCongruence.lean`,
using the source's simplification proof.
-/

universe u v w

namespace Langlands.NYLL.LubinTate

/-- Equal parameter images give equal images of the standard
Lubin--Tate polynomials. -/
theorem standardLubinTatePolynomial_map_eq_of_parameter_eq :
    standardLubinTatePolynomial_map_eq_of_parameter_eqStatement.{u, v, w} := by
  intro K _ F R _ f π ϖ h
  simp [standardLubinTatePolynomial, h]

end Langlands.NYLL.LubinTate
