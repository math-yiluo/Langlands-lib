/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice.U108.Definitions

/-! Source theorem targets M144.109, .115 and .119; see Statements.md. -/

namespace Langlands.NYLL.CyclicCohomology

noncomputable section

universe u

open scoped ValuativeRel

variable (L : Type u) [Field L] [ValuativeRel L]

def mem_chosenNormalBasisPrincipalUnitSuccSubgroup_iffStatement
    {Vn Vsucc : Subgroup 𝒪[L]ˣ} (hV : Vsucc ≤ Vn) (u : Vn) : Prop :=
    u ∈ chosenNormalBasisPrincipalUnitSuccSubgroup (L := L) hV ↔
      (u : 𝒪[L]ˣ) ∈ Vsucc

def chosenNormalBasisPrincipalUnitSuccQuotMk_surjectiveStatement
    {Vn Vsucc : Subgroup 𝒪[L]ˣ} (hV : Vsucc ≤ Vn) : Prop :=
    Function.Surjective
      (chosenNormalBasisPrincipalUnitSuccQuotMk (L := L) hV)

def chosenNormalBasisPrincipalUnitSuccQuotMk_eq_one_iffStatement
    {Vn Vsucc : Subgroup 𝒪[L]ˣ} (hV : Vsucc ≤ Vn) (u : Vn) : Prop :=
    chosenNormalBasisPrincipalUnitSuccQuotMk (L := L) hV u = 1 ↔
      (u : 𝒪[L]ˣ) ∈ Vsucc

end

end Langlands.NYLL.CyclicCohomology
