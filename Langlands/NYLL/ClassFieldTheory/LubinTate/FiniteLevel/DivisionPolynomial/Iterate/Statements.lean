/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Extracted and adapted by Worker 417, 2026-11-14: the statements of
M339.010–013 (source lines 146, 156, 166, 184) of upstream commit
fbd320cd8b1b06487c58227e92eb135794267709, recast as Prop-valued
definitions named `<source name>Statement`, without proofs;
Langlands.NYLL namespace prefix, focused imports and new module
documentation. See the paired Markdown for the full record.
The retained license and notices are in licenses/NYLL/.
-/
import Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.DivisionPolynomial.Iterate.Definitions
import Mathlib.Algebra.Polynomial.Degree.Defs

/-!
# Basic statements about standard Lubin--Tate polynomial iterates

Successor recursion, degree, monicity and vanishing at zero of the
compositional iterates, as proposition-valued targets. No proofs are given.
-/

noncomputable section

universe u v

namespace Langlands.NYLL.LubinTate

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]

/-- M339.010: a successor iterate is obtained by one further composition
with the standard polynomial. -/
def standardLubinTatePolynomialIterate_succStatement
    (F : LocalField.{u, v} K) (π : F.valuationSubring) (n : ℕ) : Prop :=
  standardLubinTatePolynomialIterate F π (n + 1) =
    (standardLubinTatePolynomial F π).comp
      (standardLubinTatePolynomialIterate F π n)

/-- M339.011: the `n`-fold standard compositional iterate has degree
`q ^ n`, where `q` is the residue-field cardinality. -/
def standardLubinTatePolynomialIterate_natDegreeStatement
    (F : LocalField.{u, v} K) (π : F.valuationSubring) (n : ℕ) : Prop :=
  (standardLubinTatePolynomialIterate F π n).natDegree =
    Nat.card F.residueField ^ n

/-- M339.012: every compositional iterate of the standard polynomial is
monic. -/
def standardLubinTatePolynomialIterate_monicStatement
    (F : LocalField.{u, v} K) (π : F.valuationSubring) (n : ℕ) : Prop :=
  (standardLubinTatePolynomialIterate F π n).Monic

/-- M339.013: every standard compositional iterate vanishes at zero. -/
def standardLubinTatePolynomialIterate_eval_zeroStatement
    (F : LocalField.{u, v} K) (π : F.valuationSubring) (n : ℕ) : Prop :=
  (standardLubinTatePolynomialIterate F π n).eval 0 = 0

end Langlands.NYLL.LubinTate

end
