/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.GaloisIntegerRing.Definitions

/-!
# Evaluation targets for restriction to an integral-closure valuation ring

Adapted by Worker 599 from NYLL M139.003–004 on 26 October 2026.
The namespace is prefixed by `Langlands.NYLL`; the two source theorem types
are packaged as closed proposition definitions over an arbitrary shared universe.
Only the published restriction definition is imported. No evaluation proof is
exported here. See the paired Markdown for correspondence and attribution.
-/

namespace Langlands.NYLL.LocalFieldTheory

universe u

open scoped ValuativeRel

/-- The forward restriction has the same ambient-field value as the supplied
field automorphism. This is the closed statement target for NYLL M139.003. -/
def GaloisGroupIntegerRingEquivOfIsIntegralClosureApplyStatement : Prop :=
  ∀ (K L : Type u) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
    [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] (σ : Gal(L/K)) (x : 𝒪[L]),
    ((galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ x : 𝒪[L]) : L) =
      σ (x : L)

/-- The inverse restriction has the same ambient-field value as the inverse
field automorphism. This is the closed statement target for NYLL M139.004. -/
def GaloisGroupIntegerRingEquivOfIsIntegralClosureSymmApplyStatement : Prop :=
  ∀ (K L : Type u) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
    [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] (σ : Gal(L/K)) (x : 𝒪[L]),
    (((galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ).symm x : 𝒪[L]) : L) =
      σ.symm (x : L)

end Langlands.NYLL.LocalFieldTheory
