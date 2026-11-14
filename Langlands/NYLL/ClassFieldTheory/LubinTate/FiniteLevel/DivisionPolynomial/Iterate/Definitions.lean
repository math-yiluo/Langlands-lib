/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Extracted and adapted by Worker 417, 2026-11-14: only M339.008
(source line 132) of upstream commit
fbd320cd8b1b06487c58227e92eb135794267709; Langlands.NYLL namespace
prefix, focused imports of the published M339.001 definition and of
Mathlib polynomial composition, and new module documentation. See the
paired Markdown for the full record.
The retained license and notices are in licenses/NYLL/.
-/
import Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.DivisionPolynomial.Definitions
import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# Compositional iterates of the standard Lubin--Tate polynomial

This module extracts the iterate definition from
`Nyll/ClassFieldTheory/LubinTate/FiniteLevel/DivisionPolynomial.lean`.
-/

noncomputable section

universe u v

namespace Langlands.NYLL.LubinTate

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]

/-- The `n`-fold compositional iterate of the standard polynomial, starting
from `X`. -/
noncomputable def standardLubinTatePolynomialIterate
    (F : LocalField.{u, v} K) (π : F.valuationSubring) (n : ℕ) :
    Polynomial F.valuationSubring :=
  (standardLubinTatePolynomial F π).comp^[n] Polynomial.X

end Langlands.NYLL.LubinTate

end
