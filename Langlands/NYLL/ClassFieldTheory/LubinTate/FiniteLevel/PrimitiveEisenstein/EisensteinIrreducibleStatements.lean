/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 420, 2026-11-14: extract only the statements of
M340.004 and M340.006 (lines 87–91 and 126–129) from upstream commit
fbd320cd8b1b06487c58227e92eb135794267709; qualify the namespace and the
opened namespace with Langlands.NYLL, replace each theorem by a
Prop-valued definition whose name has the suffix Statement, disable
the unused-variables linter for each definition (the retained binder hπ
is unused in the Prop bodies), replace the source imports by focused
imports, and replace the module documentation. See the paired
Markdown. The retained license and notices are in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.DivisionPolynomial.Primitive.Definitions
import Mathlib.RingTheory.Polynomial.Eisenstein.Basic

/-!
# Eisenstein and irreducibility targets for the standard primitive polynomials

This module states, as Prop-valued targets, the two assertions M340.004 and
M340.006 of `Nyll/ClassFieldTheory/LubinTate/FiniteLevel/PrimitiveEisenstein.lean`:
for a uniformizer `π` of a local field `F`, the primitive quotient polynomial
`Qₙ(X) = (f^[n](X)) ^ (q - 1) + π` is Eisenstein at the maximal ideal of the
valuation ring, and it is irreducible. No proof is supplied here.
-/

noncomputable section

open scoped Polynomial

universe u v

namespace Langlands.NYLL.LubinTate

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]

set_option linter.unusedVariables false in
/-- The standard primitive quotient polynomial is Eisenstein at the maximal
ideal of the valuation ring. -/
def standardLubinTatePrimitivePolynomial_isEisensteinAtStatement
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ) : Prop :=
  (standardLubinTatePrimitivePolynomial F π n).IsEisensteinAt
    F.maximalIdeal

set_option linter.unusedVariables false in
/-- The standard primitive quotient polynomial is irreducible by
Eisenstein's criterion. -/
def standardLubinTatePrimitivePolynomial_irreducibleStatement
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ) : Prop :=
  Irreducible (standardLubinTatePrimitivePolynomial F π n)

end Langlands.NYLL.LubinTate

end
