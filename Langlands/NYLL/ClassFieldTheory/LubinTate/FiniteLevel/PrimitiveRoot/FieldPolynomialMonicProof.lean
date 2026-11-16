/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 808, 2026-11-16: extract only M341.005 (lines 90–94)
from upstream commit fbd320cd8b1b06487c58227e92eb135794267709;
prefix the namespace with Langlands.NYLL, use the fully applied published
target as the theorem type, and import the published primitive monicity
proof. Make the coefficient map explicit. See the paired Markdown.
License and notices: licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.PrimitiveRoot.FieldPolynomialStatements
import Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.DivisionPolynomial.Primitive.MonicProof

/-!
# Monicity of the primitive Lubin--Tate polynomial over the base field

The published valuation-ring primitive polynomial is monic. Mapping its
coefficients to the base field preserves monicity.
-/

noncomputable section

universe u v

namespace Langlands.NYLL.LubinTate

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]

/-- M341.005: the field-valued primitive polynomial is monic. -/
theorem standardLubinTatePrimitivePolynomialOverField_monic
    (F : LocalField.{u, v} K) (π : F.valuationSubring) (n : ℕ) :
    standardLubinTatePrimitivePolynomialOverField_monicStatement F π n := by
  change ((standardLubinTatePrimitivePolynomial F π n).map
    (algebraMap F.valuationSubring K)).Monic
  exact (standardLubinTatePrimitivePolynomial_monic F π n).map
    (algebraMap F.valuationSubring K)

end Langlands.NYLL.LubinTate

end
