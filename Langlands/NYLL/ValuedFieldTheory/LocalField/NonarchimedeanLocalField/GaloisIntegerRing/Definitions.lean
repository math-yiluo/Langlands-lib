/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.RingTheory.Valuation.Extension
import Mathlib.Topology.Algebra.Valued.ValuativeRel

/-!
# Restriction to an integral-closure valuation ring

Adapted by Worker 104 from NYLL M139.002 on 25 October 2026.
The namespace is prefixed by `Langlands.NYLL`; only this data definition is retained.
The construction uses Mathlib's `galRestrict'` instead of the source preservation theorem.
Imports are reduced to Mathlib. See the paired Markdown for source and attribution details.
-/

namespace Langlands.NYLL.LocalFieldTheory

noncomputable section

universe u

open scoped ValuativeRel

/-- Restrict a field automorphism to the canonical integer ring, using its integral-closure
property and Mathlib's restriction of algebra homomorphisms. -/
def galoisGroupIntegerRingEquivOfIsIntegralClosure
    (K L : Type u) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
    [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] (σ : Gal(L/K)) :
    𝒪[L] ≃+* 𝒪[L] :=
  (AlgEquiv.ofAlgHom
    (galRestrict' 𝒪[K] 𝒪[L] 𝒪[L] σ.toAlgHom)
    (galRestrict' 𝒪[K] 𝒪[L] 𝒪[L] σ.symm.toAlgHom)
    (by simp [← galRestrict'_comp])
    (by simp [← galRestrict'_comp])).toRingEquiv

end

end Langlands.NYLL.LocalFieldTheory
