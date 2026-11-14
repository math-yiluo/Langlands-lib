/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 418, 2026-11-14: extract only the statements of
M339.016 (lines 215–220), M339.017 (lines 237–240), M339.018
(lines 261–265) and M339.019 (lines 273–279) from upstream commit
fbd320cd8b1b06487c58227e92eb135794267709 as Prop-valued targets named
with the suffix Statement; qualify the namespace with Langlands.NYLL;
omit the source proofs and the simp attribute of M339.018; replace the
source imports by the published M339.014 definition module and the
focused Mathlib degree module; drop the unused scoped opens; replace the
module documentation. See the paired Markdown for the full record.
The retained license and notices are in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.DivisionPolynomial.Primitive.Definitions
import Mathlib.Algebra.Polynomial.Degree.Defs

/-!
# Targets for the primitive Lubin--Tate quotient polynomial

This module states, as propositions without proofs, that the primitive
quotient polynomial `Qₙ = (f^[n]) ^ (q - 1) + π` has natural degree
`(q - 1) * q ^ n`, is monic and has constant coefficient `π`, and that
`f^[n+1] = f^[n] * Qₙ`. Here `f(X) = X ^ q + π * X` is the standard
Lubin--Tate polynomial and `q` is the natural cardinality of the residue
field. It extracts the statements of M339.016–019 from
`Nyll/ClassFieldTheory/LubinTate/FiniteLevel/DivisionPolynomial.lean`.
-/

noncomputable section

universe u v

namespace Langlands.NYLL.LubinTate

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]

/-- M339.016: the primitive quotient polynomial has degree
`(q - 1) * q ^ n`. -/
def standardLubinTatePrimitivePolynomial_natDegreeStatement
    (F : LocalField.{u, v} K) (π : F.valuationSubring) (n : ℕ) : Prop :=
  (standardLubinTatePrimitivePolynomial F π n).natDegree =
    (Nat.card F.residueField - 1) *
      Nat.card F.residueField ^ n

/-- M339.017: the primitive quotient polynomial is monic. -/
def standardLubinTatePrimitivePolynomial_monicStatement
    (F : LocalField.{u, v} K) (π : F.valuationSubring) (n : ℕ) : Prop :=
  (standardLubinTatePrimitivePolynomial F π n).Monic

/-- M339.018: the constant coefficient of the primitive quotient
polynomial is `π`. -/
def standardLubinTatePrimitivePolynomial_coeff_zeroStatement
    (F : LocalField.{u, v} K) (π : F.valuationSubring) (n : ℕ) : Prop :=
  (standardLubinTatePrimitivePolynomial F π n).coeff 0 = π

/-- M339.019: the next compositional iterate is the current iterate times
its primitive quotient polynomial. -/
def standardLubinTatePolynomialIterate_succ_factorStatement
    (F : LocalField.{u, v} K) (π : F.valuationSubring) (n : ℕ) : Prop :=
  standardLubinTatePolynomialIterate F π (n + 1) =
    standardLubinTatePolynomialIterate F π n *
      standardLubinTatePrimitivePolynomial F π n

end Langlands.NYLL.LubinTate

end
