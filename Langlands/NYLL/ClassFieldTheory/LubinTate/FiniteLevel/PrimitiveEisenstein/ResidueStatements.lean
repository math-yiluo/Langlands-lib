/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 419, 2026-11-14: extract only the statements of
M340.001–003 from upstream commit fbd320cd8b1b06487c58227e92eb135794267709;
prefix the namespace with Langlands.NYLL, replace each theorem by a
Prop-valued definition with `Statement` appended, omit the proofs, replace
the source imports by the published M339.014 definition module (which
provides M339.001 and M339.008 transitively), drop the unused scoped open,
and replace the module documentation. See the paired Markdown for the full
record. The retained license and notices are in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.DivisionPolynomial.Primitive.Definitions

/-!
# Residue reduction targets for the standard division polynomials

Prop-valued targets for the reductions modulo the maximal ideal of the
standard Lubin--Tate polynomial `X ^ q + π * X`, its compositional iterates
and the primitive quotient polynomials. No proofs are supplied here.
-/

noncomputable section

universe u v

namespace Langlands.NYLL.LubinTate

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]

set_option linter.unusedVariables false in
/-- M340.001: reduction modulo the maximal ideal sends the standard
Lubin--Tate polynomial to `X ^ q`. -/
def standardLubinTatePolynomial_map_residueStatement
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) : Prop :=
  (standardLubinTatePolynomial F π).map F.residueMap =
    Polynomial.X ^ Nat.card F.residueField

set_option linter.unusedVariables false in
/-- M340.002: reduction modulo the maximal ideal sends the `n`-fold
standard iterate to `X ^ (q ^ n)`. -/
def standardLubinTatePolynomialIterate_map_residueStatement
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ) : Prop :=
  (standardLubinTatePolynomialIterate F π n).map F.residueMap =
    Polynomial.X ^ (Nat.card F.residueField ^ n)

set_option linter.unusedVariables false in
/-- M340.003: reduction modulo the maximal ideal sends the primitive
quotient polynomial to its leading monomial. -/
def standardLubinTatePrimitivePolynomial_map_residueStatement
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K)) (n : ℕ) : Prop :=
  (standardLubinTatePrimitivePolynomial F π n).map F.residueMap =
    Polynomial.X ^
      ((Nat.card F.residueField - 1) *
        Nat.card F.residueField ^ n)

end Langlands.NYLL.LubinTate

end
