/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 416, 2026-11-14: extract only M339.006 (lines 100–104)
and M339.007 (lines 116–119) from upstream commit
fbd320cd8b1b06487c58227e92eb135794267709 as Prop-valued targets named with
the suffix Statement; qualify the namespace with Langlands.NYLL; omit the
source proofs; replace the source imports by the published definition module
and the focused Mathlib degree module; replace the module documentation.
The retained license and notices are in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.DivisionPolynomial.Definitions
import Mathlib.Algebra.Polynomial.Degree.Defs

/-!
# Degree and monicity targets for the standard Lubin--Tate polynomial

This module states, as propositions without proofs, that the standard
Lubin--Tate polynomial `X ^ q + π * X` has natural degree `q` and is monic,
where `q` is the natural cardinality of the residue field. It extracts the
statements of M339.006 and M339.007 from
`Nyll/ClassFieldTheory/LubinTate/FiniteLevel/DivisionPolynomial.lean`.
-/

noncomputable section

universe u v

namespace Langlands.NYLL.LubinTate

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]

/-- M339.006: the standard Lubin--Tate polynomial has degree `q`. -/
def standardLubinTatePolynomial_natDegreeStatement
    (F : LocalField.{u, v} K) (π : F.valuationSubring) : Prop :=
  (standardLubinTatePolynomial F π).natDegree =
    Nat.card F.residueField

/-- M339.007: the standard Lubin--Tate polynomial is monic. -/
def standardLubinTatePolynomial_monicStatement
    (F : LocalField.{u, v} K) (π : F.valuationSubring) : Prop :=
  (standardLubinTatePolynomial F π).Monic

end Langlands.NYLL.LubinTate

end
