/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modified by Worker 187 on 2026-11-14: extracted M144.027, prefixed the
namespace with Langlands.NYLL, applied the exact named statement target
and supplied private adaptations of the normal-basis lattice prerequisites.
The paired Markdown records the source correspondence and modifications.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice.U015.Statements
import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice.U015.U025.Proofs

namespace Langlands.NYLL.CyclicCohomology

noncomputable section

universe u

open scoped ValuativeRel

variable (K L : Type u) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L] [ValuativeRel K]

private theorem normalBasisProduct_lattice_fg :
    (chosenNormalBasisIntegerLattice K L).FG := by
  dsimp [chosenNormalBasisIntegerLattice]
  exact Submodule.fg_span (Set.finite_range _)

private theorem normalBasisProduct_lattice_field_span :
    Submodule.span K
      ((chosenNormalBasisIntegerLattice K L : Submodule 𝒪[K] L) : Set L) = ⊤ := by
  refine le_antisymm le_top ?_
  rw [← (IsGalois.normalBasis K L).span_eq]
  refine Submodule.span_mono ?_
  rintro x ⟨σ, rfl⟩
  rw [IsGalois.normalBasis_apply]
  exact Submodule.subset_span (Set.mem_range_self σ)

variable [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-- Sufficiently deep powers of the chosen normal-basis lattice are closed under products. -/
theorem exists_chosenBaseUniformizerPow_chosenNormalBasisIntegerLattice_mul_mul_mem_self :
    exists_chosenBaseUniformizerPow_chosenNormalBasisIntegerLattice_mul_mul_mem_selfStatement
      K L := by
  exact exists_chosenBaseUniformizerPowSubmodule_mul_mul_mem_self_of_fg_of_field_span_eq_top
    (K := K) (L := L) (M := chosenNormalBasisIntegerLattice K L)
    (normalBasisProduct_lattice_fg K L) (normalBasisProduct_lattice_field_span K L)

end
end Langlands.NYLL.CyclicCohomology
