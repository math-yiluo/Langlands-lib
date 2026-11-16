/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

-- Modified by Worker 197: reuse published M152.023 by Lean name and check
-- its complete effective source telescope. See GaloisLinearEquiv.md.

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.NormalBasis.LatticeMaps.Definitions

namespace Langlands.NYLL.LocalClassFieldTheory

noncomputable section

universe u

open CyclicCohomology
open scoped ValuativeRel

example (K L : Type u) [Field K] [ValuativeRel K] [Field L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] (τ : Gal(L/K)) :
    chosenNormalBasisIntegerLattice K L ≃ₗ[𝒪[K]]
      chosenNormalBasisIntegerLattice K L :=
  galoisGroupChosenNormalBasisIntegerLatticeLinearEquiv K L τ

end

end Langlands.NYLL.LocalClassFieldTheory
