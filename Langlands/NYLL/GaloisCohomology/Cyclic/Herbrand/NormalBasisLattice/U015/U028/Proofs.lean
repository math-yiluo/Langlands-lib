/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modified by Worker 339 on 2026-11-14: extracted M144.028, prefixed the
namespace with Langlands.NYLL and used the exact named statement target.
The normal-basis finite-generation and full-span facts are proved locally;
the full-span argument was developed jointly with Worker 187.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice.U015.Statements
import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice.U015.U026.Proofs

namespace Langlands.NYLL.CyclicCohomology

noncomputable section

universe u

open scoped ValuativeRel

variable (K L : Type u) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-- Deep normal-basis lattice products lie one uniformizer step deeper (M144.028). -/
theorem exists_chosenBaseUniformizerPow_chosenNormalBasisIntegerLattice_mul_mul_mem_succ :
    exists_chosenBaseUniformizerPow_chosenNormalBasisIntegerLattice_mul_mul_mem_succStatement
      K L := by
  have hfg : (chosenNormalBasisIntegerLattice K L).FG := by
    dsimp [chosenNormalBasisIntegerLattice]
    exact Submodule.fg_span (Set.finite_range _)
  have hspan :
      Submodule.span K ((chosenNormalBasisIntegerLattice K L : Submodule 𝒪[K] L) : Set L) =
        ⊤ := by
    refine le_antisymm le_top ?_
    rw [← (IsGalois.normalBasis K L).span_eq]
    refine Submodule.span_mono ?_
    rintro x ⟨σ, rfl⟩
    rw [IsGalois.normalBasis_apply]
    exact Submodule.subset_span (Set.mem_range_self σ)
  exact exists_chosenBaseUniformizerPowSubmodule_mul_mul_mem_succ_of_fg_of_field_span_eq_top
    (K := K) (L := L) (M := chosenNormalBasisIntegerLattice K L) hfg hspan

end
end Langlands.NYLL.CyclicCohomology
