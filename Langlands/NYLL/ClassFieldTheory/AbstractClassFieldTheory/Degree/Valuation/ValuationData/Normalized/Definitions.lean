/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Valuation.ValuationData.Definitions
import Langlands.NYLL.GaloisCohomology.ProfiniteIntegers.ProfiniteInteger.Divide.U018.Proofs

/-!
# The normalized valuation `v_K = (1/f_K) v ∘ N_{K|k}`

Modified by Worker 5264, 14 November 2026: extract M025.021, M025.022 and
M025.025 from
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/Valuation.lean`
at fbd320cd8b1b06487c58227e92eb135794267709, prefix the namespace with
`Langlands.NYLL`, and replace the source's module imports by the published
valuation-data module and the published proof of M009.018
(`zHatDivide_zHatMulNat`), which transitively imports `zHatDivide`.
In the body of M025.021 the rewrite with the theorem M025.020
(`normCompositeAt_range`) uses a local copy of that statement proved by the
structure field `v.norm_range K`, its source proof. In the body of M025.025
the theorem M025.024 (`dividedAt_mem_valueGroup`) is replaced by its source
proof, inlined in the same way. Universes, binders, docstrings and the
remaining bodies are unchanged. See the paired Markdown and
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.ClassFormation

open KummerTheory

open CyclicCohomology

noncomputable section

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

namespace ValuationData

variable {D : DegreeData G} {A : Rep ℤ G}

/-- `v(N_{K|k}a)` regarded as an element of `f_K ℤ̂`. -/
def normCompositeAtInResidueImage (v : ValuationData D A)
    (K : FiniteAbstractField G) :
    ambientFixedAddSubgroup A K.field →+
      (zHatMulNat (K.residueDegree D : ℕ)).toAddMonoidHom.range where
  toFun a := ⟨v.normCompositeAt K a, by
    have ha : v.normCompositeAt K a ∈ (v.normCompositeAt K).range := ⟨a, rfl⟩
    have hrange : (v.normCompositeAt K).range =
        nsmulImage v.valueGroup (K.residueDegree D : ℕ) := v.norm_range K
    rw [hrange] at ha
    obtain ⟨z, _hz, hz⟩ := ha
    exact ⟨z, hz⟩⟩
  map_zero' := by ext; simp [normCompositeAt]
  map_add' x y := by
    apply Subtype.ext
    exact map_add (v.normCompositeAt K) x y

/-- Division by `f_K` before restricting the codomain back to `Z`. -/
def dividedAt (v : ValuationData D A) (K : FiniteAbstractField G) :
    ambientFixedAddSubgroup A K.field →+ ZHat :=
  (zHatDivide (K.residueDegree D : ℕ)
    (K.residueDegree D).property).toAddMonoidHom.comp
      (v.normCompositeAtInResidueImage K)

/-- The normalized valuation `v_K = (1/f_K) v ∘ N_{K|k}`, with the exact
codomain `Z` from the valuation-quotient axiom. -/
def valuationAt (v : ValuationData D A) (K : FiniteAbstractField G) :
    ambientFixedAddSubgroup A K.field →+ v.valueGroup :=
  (v.dividedAt K).codRestrict v.valueGroup (fun a => by
    have ha : v.normCompositeAt K a ∈ (v.normCompositeAt K).range := ⟨a, rfl⟩
    have hrange : (v.normCompositeAt K).range =
        nsmulImage v.valueGroup (K.residueDegree D : ℕ) := v.norm_range K
    rw [hrange] at ha
    obtain ⟨z, hzZ, hz⟩ := ha
    have hzSubtype : v.normCompositeAtInResidueImage K a =
        ⟨zHatMulNat (K.residueDegree D : ℕ) z, ⟨z, rfl⟩⟩ := by
      apply Subtype.ext
      change v.normCompositeAt K a =
        zHatMulNat (K.residueDegree D : ℕ) z
      exact hz.symm
    change zHatDivide (K.residueDegree D : ℕ)
        (K.residueDegree D).property
          (v.normCompositeAtInResidueImage K a) ∈ v.valueGroup
    rw [hzSubtype]
    exact (zHatDivide_zHatMulNat (K.residueDegree D : ℕ)
      (K.residueDegree D).property z).symm ▸ hzZ)

end ValuationData

end

end Langlands.NYLL.ClassFormation
