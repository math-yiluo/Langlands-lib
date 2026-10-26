/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.GaloisIntegerRing.Definitions

/-!
# Residue-field equivalence from an integral-closure restriction

Adapted by Worker 601 from NYLL M160.001 on 26 October 2026.
The namespace is prefixed by `Langlands.NYLL`; only this data definition is retained.
The original broad imports are replaced by Mathlib's residue-field construction and
the published integer-ring equivalence. See the paired Markdown for source and attribution.
-/

namespace Langlands.NYLL.LocalFieldTheory

noncomputable section

universe u

open scoped ValuativeRel

/-- Descend the integral-closure restriction of a field automorphism to the actual
residue field of its valuation integer ring. -/
def galoisGroupResidueFieldEquivOfIsIntegralClosure (K L : Type u)
    [Field K] [ValuativeRel K] [Field L] [ValuativeRel L] [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] (σ : Gal(L/K)) :
    𝓀[L] ≃+* 𝓀[L] :=
  IsLocalRing.ResidueField.mapEquiv
    (galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ)

end

end Langlands.NYLL.LocalFieldTheory
