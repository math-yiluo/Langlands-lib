/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 418, 2026-11-14: extract only M339.014 (lines 198–204)
from upstream commit fbd320cd8b1b06487c58227e92eb135794267709; qualify
the namespace with Langlands.NYLL, replace the source imports by the
published M339.008 iterate module, drop the unused scoped opens, and
replace the module documentation. See the paired Markdown for the full
record. The retained license and notices are in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.DivisionPolynomial.Iterate.Definitions

/-!
# The primitive quotient of the standard Lubin--Tate division polynomials

For a local field package `F`, an element `π` of its valuation ring and
`n : ℕ`, this module defines the polynomial
`Qₙ(X) = (f^[n](X)) ^ (q - 1) + π` over the valuation ring, where
`f(X) = X ^ q + π * X` is the standard Lubin--Tate polynomial and `q` is
the natural cardinality of the residue field. It extracts M339.014 from
`Nyll/ClassFieldTheory/LubinTate/FiniteLevel/DivisionPolynomial.lean`.
No uniformizer hypothesis on `π` is made.
-/

noncomputable section

universe u v

namespace Langlands.NYLL.LubinTate

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]

/-- The primitive quotient polynomial at level `n + 1`. -/
noncomputable def standardLubinTatePrimitivePolynomial
    (F : LocalField.{u, v} K) (π : F.valuationSubring) (n : ℕ) :
    Polynomial F.valuationSubring :=
  standardLubinTatePolynomialIterate F π n ^
      (Nat.card F.residueField - 1) +
    Polynomial.C π

end Langlands.NYLL.LubinTate

end
