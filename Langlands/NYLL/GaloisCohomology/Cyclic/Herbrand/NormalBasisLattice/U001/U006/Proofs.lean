/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modified by Worker 516 on 2026-11-14: ported M144.006 to the
Langlands.NYLL namespace and proved the published Statement target.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice.U001.Statements

namespace Langlands.NYLL.CyclicCohomology

noncomputable section

universe u
open scoped ValuativeRel

variable (K L : Type u) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]
  [ValuativeRel K]

/-- The chosen integer lattice spans the extension field over the base field. -/
theorem chosenNormalBasisIntegerLattice_field_span_eq_top :
    chosenNormalBasisIntegerLattice_field_span_eq_topStatement K L := by
  unfold chosenNormalBasisIntegerLattice_field_span_eq_topStatement
  have hspan :
      Submodule.span K
        (Set.range (fun σ : Gal(L/K) =>
          σ (IsGalois.normalBasis K L (1 : Gal(L/K))))) = ⊤ := by
    have hset :
        Set.range (fun σ : Gal(L/K) =>
          σ (IsGalois.normalBasis K L (1 : Gal(L/K)))) =
          Set.range (IsGalois.normalBasis K L) := by
      ext x
      constructor
      · rintro ⟨σ, rfl⟩
        exact ⟨σ, IsGalois.normalBasis_apply (K := K) (L := L) σ⟩
      · rintro ⟨σ, rfl⟩
        exact ⟨σ, (IsGalois.normalBasis_apply (K := K) (L := L) σ).symm⟩
    rw [hset]
    exact (IsGalois.normalBasis K L).span_eq
  refine le_antisymm le_top ?_
  rw [← hspan]
  refine Submodule.span_mono ?_
  intro x hx
  exact Submodule.subset_span hx

end
end Langlands.NYLL.CyclicCohomology
