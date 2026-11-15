/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 421, 2026-11-14: extract the statements of M341.005,
M341.006 and M341.007 (lines 90–120) from upstream commit
fbd320cd8b1b06487c58227e92eb135794267709 as Prop-valued definitions;
prefix the namespace with Langlands.NYLL, omit the proofs and use
focused imports. See the paired Markdown. License and notices:
licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.PrimitiveRoot.FieldPolynomial
import Mathlib.Algebra.Group.Irreducible.Defs

/-!
# Monicity, degree and irreducibility targets for the field polynomial

Prop-valued targets for three theorems of
`Nyll/ClassFieldTheory/LubinTate/FiniteLevel/PrimitiveRoot.lean`.
-/

noncomputable section

open scoped Polynomial

universe u v

namespace Langlands.NYLL.LubinTate

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]

/-- M341.005: the field-valued primitive polynomial is monic. -/
def standardLubinTatePrimitivePolynomialOverField_monicStatement
    (F : LocalField.{u, v} K) (π : F.valuationSubring) (n : ℕ) : Prop :=
  (standardLubinTatePrimitivePolynomialOverField F π n).Monic

/-- M341.006: the field-valued primitive polynomial has degree
`(q - 1) * q ^ n`. -/
def standardLubinTatePrimitivePolynomialOverField_natDegreeStatement
    (F : LocalField.{u, v} K) (π : F.valuationSubring) (n : ℕ) : Prop :=
  (standardLubinTatePrimitivePolynomialOverField F π n).natDegree =
    (Nat.card F.residueField - 1) *
      Nat.card F.residueField ^ n

/-- M341.007: for a uniformizer `π`, the field-valued primitive polynomial is
irreducible. -/
def standardLubinTatePrimitivePolynomialOverField_irreducibleStatement
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (_hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ) : Prop :=
  Irreducible (standardLubinTatePrimitivePolynomialOverField F π n)

end Langlands.NYLL.LubinTate

end
