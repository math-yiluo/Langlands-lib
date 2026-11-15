/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 423, 2026-11-14: extract the statements of M341.009–011
(lines 148–151, 191–194 and 200–205) from NYLL at pinned commit
fbd320cd8b1b06487c58227e92eb135794267709, prefix the namespace with
Langlands.NYLL, replace each theorem by a Prop-valued definition named
with the suffix `Statement`, omit all proofs and use focused imports.
See the paired Markdown for the complete modification record.
License and notices: licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.PrimitiveRoot.FieldPolynomial
import Mathlib.FieldTheory.IsSepClosed

/-!
# Separability and root-existence targets for the primitive polynomial

Prop-valued targets for NYLL M341.009–011: the field-valued primitive
Lubin–Tate polynomial has nonzero derivative, is separable, and has a root
in `SeparableClosure K`.
-/

noncomputable section

open scoped Polynomial

universe u v

namespace Langlands.NYLL.LubinTate

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]

/-- M341.009: the field-valued primitive polynomial has nonzero
derivative. -/
def standardLubinTatePrimitivePolynomialOverField_derivative_ne_zeroStatement
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (_hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ) : Prop :=
  (standardLubinTatePrimitivePolynomialOverField F π n).derivative ≠ 0

/-- M341.010: the field-valued primitive polynomial is separable. -/
def standardLubinTatePrimitivePolynomialOverField_separableStatement
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (_hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ) : Prop :=
  (standardLubinTatePrimitivePolynomialOverField F π n).Separable

/-- M341.011: the field-valued primitive polynomial has a root in
`SeparableClosure K`. -/
def exists_standardLubinTatePrimitivePolynomialOverField_rootStatement
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (_hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ) : Prop :=
  ∃ x : SeparableClosure K,
    ((standardLubinTatePrimitivePolynomialOverField F π n).map
      (algebraMap K (SeparableClosure K))).IsRoot x

end Langlands.NYLL.LubinTate
