/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 343, 2026-11-16: extract only the type of M392.002
(lines 54–69) at upstream commit fbd320cd8b1b06487c58227e92eb135794267709
as a closed, unproved Prop-valued target; prefix the namespace with
Langlands.NYLL and add the Statement suffix; import only the published
standard polynomial iterate definition. See the paired Markdown.
The retained license and notices are in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.DivisionPolynomial.Iterate.Definitions

/-!
# Equal-parameter polynomial iterate map target

This module extracts the type of M392.002 from
`Nyll/ClassFieldTheory/LubinTate/FiniteLevel/ParameterCongruence.lean`.
-/

universe u v w

namespace Langlands.NYLL.LubinTate

open LocalFieldTheory.DiscreteValuationField

set_option linter.unusedVariables false in
/-- Target extracted from M392.002: equal parameter images give equal images
of every compositional iterate of the corresponding standard polynomials. -/
def standardLubinTatePolynomialIterate_map_eq_of_parameter_eqStatement : Prop :=
  ∀ {K : Type u} [Field K] (F : LocalField.{u, v} K)
    {R : Type w} [CommRing R]
    (f : F.valuationSubring →+* R)
    {π ϖ : F.valuationSubring} (h : f π = f ϖ) (n : ℕ),
    (standardLubinTatePolynomialIterate F π n).map f =
      (standardLubinTatePolynomialIterate F ϖ n).map f

end Langlands.NYLL.LubinTate
