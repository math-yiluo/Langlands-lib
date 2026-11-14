/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modified by Worker 518, 14 November 2026: extract this proof from NYLL commit
fbd320cd8b1b06487c58227e92eb135794267709, prefix the namespace with
Langlands.NYLL, use the published statement as the theorem type, and replace
unpublished quotient helper lemmas by the underlying Mathlib quotient lemmas.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice.U103.Statements

namespace Langlands.NYLL.CyclicCohomology

noncomputable section

universe u

open scoped ValuativeRel

variable (K L : Type u) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L] [ValuativeRel K]
  [TopologicalSpace K] [IsNonarchimedeanLocalField K] [ValuativeRel L]

theorem chosenNormalBasisPrincipalUnitLatticeClass_mul_eq_add
    {n : Nat}
    (hmul_error : ∀ u : 𝒪[L]ˣ, u ∈ chosenNormalBasisPrincipalUnitSet K L n →
      ∀ v : 𝒪[L]ˣ, v ∈ chosenNormalBasisPrincipalUnitSet K L n →
        (((((u * v : 𝒪[L]ˣ) : 𝒪[L]) - 1 : 𝒪[L]) : L) -
            (((((u : 𝒪[L]ˣ) : 𝒪[L]) - 1 : 𝒪[L]) : L) +
              ((((v : 𝒪[L]ˣ) : 𝒪[L]) - 1 : 𝒪[L]) : L))) ∈
          chosenBaseUniformizerPowSubmodule K L (n + 1)
            (chosenNormalBasisIntegerLattice K L))
    (u v : 𝒪[L]ˣ)
    (hu : u ∈ chosenNormalBasisPrincipalUnitSet K L n)
    (hv : v ∈ chosenNormalBasisPrincipalUnitSet K L n)
    (huv : u * v ∈ chosenNormalBasisPrincipalUnitSet K L n) :
    chosenNormalBasisPrincipalUnitLatticeClass_mul_eq_addStatement K L hmul_error u v hu hv huv := by
  unfold chosenNormalBasisPrincipalUnitLatticeClass_mul_eq_addStatement
  unfold chosenNormalBasisPrincipalUnitLatticeClass
  rw [← map_add]
  apply (Submodule.Quotient.eq (chosenNormalBasisLatticeSuccSubmodule K L n)).2
  exact hmul_error u hu v hv

end

end Langlands.NYLL.CyclicCohomology
