/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 421, 2026-11-14: extract only M341.003 (lines 71–77)
from upstream commit fbd320cd8b1b06487c58227e92eb135794267709; prefix
the namespace with Langlands.NYLL and replace the source imports by the
focused primitive division-polynomial module. See the paired Markdown.
License and notices: licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.DivisionPolynomial.Primitive.Definitions

/-!
# The primitive division polynomial over the base field

This module extracts the field-coefficient primitive division polynomial
from `Nyll/ClassFieldTheory/LubinTate/FiniteLevel/PrimitiveRoot.lean`.
-/

noncomputable section

open scoped Polynomial

universe u v

namespace Langlands.NYLL.LubinTate

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]

/-- The primitive division polynomial after extending coefficients from the
valuation ring to the base field. -/
noncomputable def standardLubinTatePrimitivePolynomialOverField
    (F : LocalField.{u, v} K) (π : F.valuationSubring) (n : ℕ) :
    Polynomial K :=
  (standardLubinTatePrimitivePolynomial F π n).map
    (algebraMap F.valuationSubring K)

end Langlands.NYLL.LubinTate

end
