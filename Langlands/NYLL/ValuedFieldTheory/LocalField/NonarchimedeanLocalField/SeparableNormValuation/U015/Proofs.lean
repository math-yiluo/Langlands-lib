/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 173, 13 November 2026:
Extract the proof of M162.015 from
Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/SeparableNormValuation.lean
at fbd320cd8b1b06487c58227e92eb135794267709 (lines 321 and 371-387).
Prefix the namespace with Langlands.NYLL, give the theorem the published
statement fractionRing_integerRing_isSeparableStatement K L as its type,
and import only the U015 Statements module. The file-level local instance
attribute on FractionRing.liftAlgebra is kept. The proof steps are
unchanged; all other source declarations are omitted. The upstream LICENSE
and NOTICE are preserved in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.SeparableNormValuation.U015.Statements

/-!
# Separability of the fraction fields of valuation integer rings

The canonical fraction fields of the valuation integer rings `𝒪[K]` and
`𝒪[L]` are copies of `K` and `L`, so separability of `L / K` transfers to
`FractionRing 𝒪[L] / FractionRing 𝒪[K]`.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

noncomputable section

universe u v

open scoped ValuativeRel

attribute [local instance] FractionRing.liftAlgebra

/-- Separability of an actual field extension transfers to the canonical
fraction fields of its valuation integer rings. -/
theorem fractionRing_integerRing_isSeparable
    (K : Type u) (L : Type v)
    [Field K] [ValuativeRel K]
    [Field L] [ValuativeRel L]
    [Algebra K L] [Algebra.IsSeparable K L]
    [Valuation.HasExtension (ValuativeRel.valuation K)
      (ValuativeRel.valuation L)] :
    fractionRing_integerRing_isSeparableStatement K L := by
  apply Algebra.IsSeparable.of_equiv_equiv
    (FractionRing.algEquiv 𝒪[K] K).symm.toRingEquiv
    (FractionRing.algEquiv 𝒪[L] L).symm.toRingEquiv
  ext x
  exact IsFractionRing.algEquiv_commutes
    (FractionRing.algEquiv 𝒪[K] K).symm
    (FractionRing.algEquiv 𝒪[L] L).symm x

end

end Langlands.NYLL.LocalClassFieldTheory
