/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 422, 2026-11-14: extract only the statements of
M341.001, M341.002 and M341.008 (lines 47–49, 56–59 and 123–125) from
upstream commit fbd320cd8b1b06487c58227e92eb135794267709; qualify the
namespace with Langlands.NYLL, replace each theorem by a Prop-valued
definition named with the suffix Statement, drop the proofs and the
simp attributes, use focused imports and replace the module
documentation. See the paired Markdown. License and notices: licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.DivisionPolynomial.Definitions
import Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.DivisionPolynomial.Iterate.Definitions
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Derivative at zero and residue cardinality targets

Prop-valued targets for three scalar computations from
`Nyll/ClassFieldTheory/LubinTate/FiniteLevel/PrimitiveRoot.lean` that
support the separability of the standard primitive division polynomials:
the derivative at zero of the standard polynomial `X ^ q + π * X` and of
its `n`-fold compositional iterate, and the nonvanishing of `q - 1` in the
base field, where `q` is the cardinality of the residue field.
-/

noncomputable section

open scoped Polynomial

universe u v

namespace Langlands.NYLL.LubinTate

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]

/-- Target (M341.001): the derivative of the standard polynomial at zero
is its linear coefficient. -/
def standardLubinTatePolynomial_derivative_eval_zeroStatement
    (F : LocalField.{u, v} K) (π : F.valuationSubring) : Prop :=
  (standardLubinTatePolynomial F π).derivative.eval 0 = π

/-- Target (M341.002): the derivative at zero of the `n`-fold standard
iterate is `π ^ n`. -/
def standardLubinTatePolynomialIterate_derivative_eval_zeroStatement
    (F : LocalField.{u, v} K) (π : F.valuationSubring) (n : ℕ) : Prop :=
  (standardLubinTatePolynomialIterate F π n).derivative.eval 0 =
    π ^ n

/-- Target (M341.008): the natural number `q - 1` is nonzero in the local
field. -/
def residueFieldNatCard_sub_one_cast_ne_zeroStatement
    (F : LocalField.{u, v} K) : Prop :=
  ((Nat.card F.residueField - 1 : ℕ) : K) ≠ 0

end Langlands.NYLL.LubinTate
