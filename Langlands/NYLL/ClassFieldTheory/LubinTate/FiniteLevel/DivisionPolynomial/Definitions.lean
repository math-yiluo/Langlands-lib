/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 416, 2026-11-14: extract only M339.001 (lines 49–55)
from upstream commit fbd320cd8b1b06487c58227e92eb135794267709; qualify
the namespace with Langlands.NYLL, replace the source imports by the
published LocalField package and focused Mathlib polynomial and
cardinality imports, and replace the module documentation.
The retained license and notices are in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.DiscreteValuationField.Basic.Definitions
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.SetTheory.Cardinal.Finite

/-!
# The standard Lubin--Tate polynomial

For a local field package `F` and an element `π` of its valuation ring, this
module defines the polynomial `X ^ q + π * X` over the valuation ring, where
`q` is the natural cardinality of the residue field. It extracts M339.001 from
`Nyll/ClassFieldTheory/LubinTate/FiniteLevel/DivisionPolynomial.lean`.
No uniformizer hypothesis on `π` is made.
-/

noncomputable section

open scoped Polynomial

universe u v

namespace Langlands.NYLL.LubinTate

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]

/-- The polynomial `X ^ q + π * X` underlying the standard Lubin--Tate
series. -/
noncomputable def standardLubinTatePolynomial
    (F : LocalField.{u, v} K) (π : F.valuationSubring) :
    Polynomial F.valuationSubring :=
  Polynomial.X ^ Nat.card F.residueField +
    Polynomial.C π * Polynomial.X

end Langlands.NYLL.LubinTate

end
