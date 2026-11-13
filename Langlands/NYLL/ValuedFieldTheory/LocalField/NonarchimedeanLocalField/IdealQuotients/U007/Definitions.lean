/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modified by Worker 85 on 2026-11-13: extracted M133.007 and M133.009
from IdealQuotients.lean at commit fbd320cd8b1b06487c58227e92eb135794267709;
added the Langlands.NYLL namespace prefix and replaced the source imports by
the published module holding the M133.005 proof. Both definition bodies,
universes and telescopes are unchanged; the source proof term inside
integerRingUniformizerFieldUnit is kept and now uses the published theorem
chosenIntegerRingUniformizer_irreducible, whose type is the published
Prop-valued target chosenIntegerRingUniformizer_irreducibleStatement.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.IdealQuotients.U005.Proofs

namespace Langlands.NYLL.LocalFieldTheory

noncomputable section

universe u

open scoped ValuativeRel

/-- The chosen DVR uniformizer of `𝒪[K]`, viewed as a nonzero field unit.

This is the source object for the local class-field decomposition by powers of
a prime element.  Valuation normalization is proved separately; it is not an
extra argument of this definition. -/
def integerRingUniformizerFieldUnit
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] : Kˣ :=
  Units.mk0 (((chosenIntegerRingUniformizer K : 𝒪[K]) : K)) (by
    intro h
    exact (chosenIntegerRingUniformizer_irreducible K).ne_zero (Subtype.ext h))

/-- The inverse of the chosen DVR uniformizer, as a field unit.

With the normalized additive valuation used by `valuationMap`, this is the
element expected to have value `1`.  The proof of that normalization is the next
source-producing frontier. -/
def inverseIntegerRingUniformizerFieldUnit
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] : Kˣ :=
  (integerRingUniformizerFieldUnit K)⁻¹

end
end Langlands.NYLL.LocalFieldTheory
