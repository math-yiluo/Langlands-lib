/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modified by Worker 516 on 2026-11-14: ported M144.001 to the
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

/-- The Galois orbit of the normal-basis generator spans the extension field. -/
theorem normalBasisConjugates_span_eq_top :
    normalBasisConjugates_span_eq_topStatement K L := by
  unfold normalBasisConjugates_span_eq_topStatement
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

end
end Langlands.NYLL.CyclicCohomology
