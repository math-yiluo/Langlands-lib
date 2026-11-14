/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.NormalBasis.SpanStatement

/-!
Modified by Worker 517: extract M152.001 from NYLL commit
fbd320cd8b1b06487c58227e92eb135794267709, adapt namespace/imports and
use its published target. Unfold the lattice instead of invoking the
source's separate definitional equality theorem M144.003. See Proofs.md.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

universe u

open CyclicCohomology
open scoped ValuativeRel

theorem span_normalBasis_eq_chosenNormalBasisIntegerLattice
    (K L : Type u)
    [Field K] [ValuativeRel K] [Field L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] :
    span_normalBasis_eq_chosenNormalBasisIntegerLatticeStatement K L := by
  unfold span_normalBasis_eq_chosenNormalBasisIntegerLatticeStatement
    chosenNormalBasisIntegerLattice
  congr 1
  ext y
  constructor
  · rintro ⟨sigma, rfl⟩
    exact ⟨sigma, (IsGalois.normalBasis_apply (K := K) (L := L) sigma).symm⟩
  · rintro ⟨sigma, rfl⟩
    exact ⟨sigma, IsGalois.normalBasis_apply (K := K) (L := L) sigma⟩

end Langlands.NYLL.LocalClassFieldTheory
