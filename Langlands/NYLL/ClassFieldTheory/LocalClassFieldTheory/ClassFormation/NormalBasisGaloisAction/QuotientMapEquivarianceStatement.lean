/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

-- Modified by Worker 197: extract M145.016 from NYLL fbd320cd as a
-- Prop-valued target, prefix the namespace and narrow the imports.
-- See QuotientMapEquivarianceStatement.md.

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.NormalBasisGaloisAction.IntegerUnitsQuotAction
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.NormalBasisGaloisAction.IntegerUnitMaps

namespace Langlands.NYLL.LocalClassFieldTheory

noncomputable section

universe u

open CyclicCohomology LocalFieldTheory
open scoped ValuativeRel

/-- The quotient map on integer units is Galois equivariant. -/
def chosenNormalBasisIntegerUnitsQuotientMap_equivariantStatement
    (K L : Type u)
    [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [ValuativeRel L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    (n : Nat) (V : Subgroup 𝒪[L]ˣ)
    (hV : (V : Set 𝒪[L]ˣ) = chosenNormalBasisPrincipalUnitSet K L n)
    (sigma : Gal(L/K)) (a : 𝒪[L]ˣ) : Prop :=
  letI := galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure K L
  letI := chosenNormalBasisIntegerUnitsQuotMulDistribMulAction K L n V hV
  chosenNormalBasisIntegerUnitsQuotientMap (L := L) V (sigma • a) =
    sigma • chosenNormalBasisIntegerUnitsQuotientMap (L := L) V a

end

end Langlands.NYLL.LocalClassFieldTheory
