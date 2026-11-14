/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 554, 2026-11-14: extract M342.001–002 from
Nyll/ClassFieldTheory/LubinTate/FiniteLevel/PrimitiveTorsion.lean,
commit fbd320cd8b1b06487c58227e92eb135794267709; qualify namespaces
with Langlands.NYLL, replace the PrimitiveRoot import by focused
polynomial-iterate and Mathlib separable-closure imports, and replace
the module documentation. The definition bodies and parameters are unchanged.
See the paired Markdown and licenses/NYLL/LICENSE and NOTICE.
-/

import Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.DivisionPolynomial.Iterate.Definitions
import Mathlib.FieldTheory.IsSepClosed

/-!
# Standard polynomial iterates over the field and its separable closure

These definitions extend the coefficients of the standard polynomial iterate
from the chosen valuation ring to the base field and its separable closure.
-/

noncomputable section

open scoped Polynomial

universe u v

namespace Langlands.NYLL.LubinTate

open Langlands.NYLL.LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]

/-- The `n`-fold standard iterate after extending coefficients from the
valuation ring to the base field. -/
noncomputable def standardLubinTatePolynomialIterateOverField
    (F : LocalField.{u, v} K) (π : F.valuationSubring) (n : ℕ) :
    Polynomial K :=
  (standardLubinTatePolynomialIterate F π n).map
    (algebraMap F.valuationSubring K)

/-- The `n`-fold standard iterate after extending coefficients to the fixed
separable closure of the base field. -/
noncomputable def standardLubinTatePolynomialIterateOverSeparableClosure
    (F : LocalField.{u, v} K) (π : F.valuationSubring) (n : ℕ) :
    Polynomial (SeparableClosure K) :=
  (standardLubinTatePolynomialIterate F π n).map
    ((algebraMap K (SeparableClosure K)).comp
      (algebraMap F.valuationSubring K))

end Langlands.NYLL.LubinTate

end
