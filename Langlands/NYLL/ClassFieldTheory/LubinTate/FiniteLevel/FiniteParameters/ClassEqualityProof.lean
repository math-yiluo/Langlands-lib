/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Extracted and adapted by Worker 440, 2026-11-14.
Namespace prefix, published proposition target and focused import; see paired Markdown.
-/
import Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.FiniteParameters.RepresentativeStatements

noncomputable section
universe u v
namespace Langlands.NYLL.LubinTate
open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField.CompleteDVF
variable {K : Type u} [Field K]

/-- M358.007: two valuation-ring units determine the same finite parameter
exactly when their quotient belongs to `U^(n + 1)`. -/
theorem standardLubinTateUnitParameterClass_eq_iff_div_mem
    (F : LocalField.{u, v} K) (n : ℕ)
    (a b : F.valuationSubringˣ) :
    standardLubinTateUnitParameterClass_eq_iff_div_memStatement F n a b := by
  change
    QuotientGroup.mk'
        (CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF (n + 1)) a =
      QuotientGroup.mk'
        (CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF (n + 1)) b ↔
      a / b ∈
        CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF (n + 1)
  exact QuotientGroup.eq_iff_div_mem

end Langlands.NYLL.LubinTate
end
