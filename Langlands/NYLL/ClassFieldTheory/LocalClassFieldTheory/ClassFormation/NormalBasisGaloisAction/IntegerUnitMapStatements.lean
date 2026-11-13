/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.NormalBasisGaloisAction.IntegerUnitMaps

/-!
Adapted by Worker 197 from NYLL commit fbd320cd8b1b06487c58227e92eb135794267709.
Representative, injectivity, surjectivity and exactness targets
See the paired Markdown for exact source correspondence and modifications.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

noncomputable section

universe u

open scoped ValuativeRel

variable (L : Type u) [Field L] [ValuativeRel L]

def chosenNormalBasisPrincipalUnitSubgroupInclusion_applyStatement
    (V : Subgroup 𝒪[L]ˣ) (a : V) : Prop :=
chosenNormalBasisPrincipalUnitSubgroupInclusion (L := L) V a = a

def chosenNormalBasisIntegerUnitsQuotientMap_applyStatement
    (V : Subgroup 𝒪[L]ˣ) (a : 𝒪[L]ˣ) : Prop :=
chosenNormalBasisIntegerUnitsQuotientMap (L := L) V a =
      QuotientGroup.mk a

def chosenNormalBasisPrincipalUnitSubgroupInclusion_injectiveStatement
    (V : Subgroup 𝒪[L]ˣ) : Prop :=
Function.Injective (chosenNormalBasisPrincipalUnitSubgroupInclusion (L := L) V)

def chosenNormalBasisIntegerUnitsQuotientMap_surjectiveStatement
    (V : Subgroup 𝒪[L]ˣ) : Prop :=
Function.Surjective (chosenNormalBasisIntegerUnitsQuotientMap (L := L) V)

def chosenNormalBasisPrincipalUnitSubgroupInclusion_range_eq_ker_quotientStatement
    (V : Subgroup 𝒪[L]ˣ) : Prop :=
MonoidHom.range (chosenNormalBasisPrincipalUnitSubgroupInclusion (L := L) V) =
      MonoidHom.ker (chosenNormalBasisIntegerUnitsQuotientMap (L := L) V)

end

end Langlands.NYLL.LocalClassFieldTheory
