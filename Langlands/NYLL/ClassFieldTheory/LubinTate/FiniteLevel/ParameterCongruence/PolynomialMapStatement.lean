/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 660, 2026-11-14: extract only the type of M392.001
(lines 43–50) at upstream commit fbd320cd8b1b06487c58227e92eb135794267709
as a closed, unproved Prop-valued target; prefix the namespace with
Langlands.NYLL and add the Statement suffix; use the published polynomial
definition and Mathlib's polynomial map API as focused imports.
The retained license and notices are in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.DivisionPolynomial.Definitions
import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# Equal-parameter polynomial map target

This module extracts the type of M392.001 from
`Nyll/ClassFieldTheory/LubinTate/FiniteLevel/ParameterCongruence.lean`.
It states that equal parameter images give equal images of the standard
Lubin--Tate polynomials.
-/

universe u v w

namespace Langlands.NYLL.LubinTate

open LocalFieldTheory.DiscreteValuationField

set_option linter.unusedVariables false in
/-- Target extracted from M392.001: equal parameter images give equal
images of the standard Lubin--Tate polynomials. -/
def standardLubinTatePolynomial_map_eq_of_parameter_eqStatement : Prop :=
  ∀ {K : Type u} [Field K] (F : LocalField.{u, v} K)
    {R : Type w} [CommRing R]
    (f : F.valuationSubring →+* R)
    {π ϖ : F.valuationSubring} (h : f π = f ϖ),
    (standardLubinTatePolynomial F π).map f =
      (standardLubinTatePolynomial F ϖ).map f

end Langlands.NYLL.LubinTate
