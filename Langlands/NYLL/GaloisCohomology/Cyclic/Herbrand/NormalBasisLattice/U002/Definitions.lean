/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modified by Worker 231 on 2026-11-13: extracted the source units recorded
in the paired Markdown; prefixed the namespace with Langlands.NYLL and
reduced imports. Source data bodies and parameter binding are preserved.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Mathlib.FieldTheory.Galois.NormalBasis
import Mathlib.NumberTheory.LocalField.Basic

namespace Langlands.NYLL.CyclicCohomology

noncomputable section

universe u

open scoped ValuativeRel
open Filter

variable (K L : Type u) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

variable [ValuativeRel K]


/-- The classical normal-basis lattice candidate `M`: the `𝒪_K`-span of the
normal-basis orbit.  Bounds comparing this lattice with `𝒪_L` are deliberately
made explicit in the lattice-comparison theorems below. -/
def chosenNormalBasisIntegerLattice : Submodule 𝒪[K] L :=
  Submodule.span 𝒪[K]
    (Set.range (fun σ : Gal(L/K) =>
      σ (IsGalois.normalBasis K L (1 : Gal(L/K)))))

end
end Langlands.NYLL.CyclicCohomology
