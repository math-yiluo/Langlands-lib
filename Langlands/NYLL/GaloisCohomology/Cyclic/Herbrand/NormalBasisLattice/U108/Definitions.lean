/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Topology.Algebra.Valued.ValuativeRel

/-!
Adapted by Worker 232 from NYLL commit fbd320cd8b1b06487c58227e92eb135794267709,
NormalBasisLattice.lean, units M144.108, .110, .111, .113 and .117.
Namespace and imports are adapted; construction bodies are unchanged.
See Definitions.md and licenses/NYLL/.
-/

namespace Langlands.NYLL.CyclicCohomology

noncomputable section

universe u

open scoped ValuativeRel

variable (L : Type u) [Field L] [ValuativeRel L]

def chosenNormalBasisPrincipalUnitSuccSubgroup {Vn Vsucc : Subgroup 𝒪[L]ˣ}
    (_hV : Vsucc ≤ Vn) : Subgroup Vn :=
  Vsucc.subgroupOf Vn

def chosenNormalBasisPrincipalUnitSuccQuot
    {Vn Vsucc : Subgroup 𝒪[L]ˣ} (hV : Vsucc ≤ Vn) : Type u :=
  Vn ⧸ chosenNormalBasisPrincipalUnitSuccSubgroup (L := L) hV

instance chosenNormalBasisPrincipalUnitSuccQuotCommGroup
    {Vn Vsucc : Subgroup 𝒪[L]ˣ} (hV : Vsucc ≤ Vn) :
    CommGroup (chosenNormalBasisPrincipalUnitSuccQuot (L := L) hV) := by
  change CommGroup
    (Vn ⧸ chosenNormalBasisPrincipalUnitSuccSubgroup (L := L) hV)
  infer_instance

def chosenNormalBasisPrincipalUnitSuccQuotMk
    {Vn Vsucc : Subgroup 𝒪[L]ˣ} (hV : Vsucc ≤ Vn) :
    Vn →* chosenNormalBasisPrincipalUnitSuccQuot (L := L) hV := by
  change Vn →*
    (Vn ⧸ chosenNormalBasisPrincipalUnitSuccSubgroup (L := L) hV)
  exact QuotientGroup.mk'
    (chosenNormalBasisPrincipalUnitSuccSubgroup (L := L) hV)

def chosenNormalBasisPrincipalUnitSuccQuotLift
    {Vn Vsucc : Subgroup 𝒪[L]ˣ} {H : Type*} [Group H]
    (hV : Vsucc ≤ Vn) (f : Vn →* H)
    (h : chosenNormalBasisPrincipalUnitSuccSubgroup (L := L) hV ≤ f.ker) :
    chosenNormalBasisPrincipalUnitSuccQuot (L := L) hV →* H := by
  change
    (Vn ⧸ chosenNormalBasisPrincipalUnitSuccSubgroup (L := L) hV) →* H
  exact QuotientGroup.lift
    (chosenNormalBasisPrincipalUnitSuccSubgroup (L := L) hV) f h

end

end Langlands.NYLL.CyclicCohomology
