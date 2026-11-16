/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 554, 2026-11-16: extract the proof of M341.006
(lines 96–105) from upstream commit fbd320cd8b1b06487c58227e92eb135794267709;
prefix the namespace with Langlands.NYLL, use focused imports, and state
the theorem with the fully applied published Prop target. See the paired
Markdown. License and notices: licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.PrimitiveRoot.FieldPolynomialStatements
import Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.DivisionPolynomial.Primitive.MonicProof
import Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.DivisionPolynomial.Primitive.NatDegreeProof

/-!
# Degree of the primitive Lubin–Tate polynomial over the base field

Exact proof of the published M341.006 target.
-/

noncomputable section

universe u v

namespace Langlands.NYLL.LubinTate

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]

/-- M341.006: extending coefficients to the base field preserves the degree
`(q - 1) * q ^ n` of the primitive division polynomial. -/
theorem standardLubinTatePrimitivePolynomialOverField_natDegree
    (F : LocalField.{u, v} K) (π : F.valuationSubring) (n : ℕ) :
    standardLubinTatePrimitivePolynomialOverField_natDegreeStatement F π n := by
  unfold standardLubinTatePrimitivePolynomialOverField_natDegreeStatement
  rw [standardLubinTatePrimitivePolynomialOverField,
    (standardLubinTatePrimitivePolynomial_monic F π n).natDegree_map,
    standardLubinTatePrimitivePolynomial_natDegree]

end Langlands.NYLL.LubinTate

end
