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

import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice.U009.Definitions
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.IdealQuotients.Definitions

namespace Langlands.NYLL.CyclicCohomology

open LocalFieldTheory

noncomputable section

universe u

open scoped ValuativeRel
open Filter

variable (K L : Type u) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

variable [ValuativeRel K]

variable [TopologicalSpace K] [IsNonarchimedeanLocalField K]


/-- Multiplication of an `𝒪_K`-submodule by a power of the chosen base
uniformizer.  The name deliberately records the construction's dependence on
`chosenIntegerRingUniformizer K`; no uniformizer-independence result is part of
this API.  This is the concrete shape of the `π_K^n` lattices used in the local
class-field-axiom calculation. -/
def chosenBaseUniformizerPowSubmodule (n : Nat) (N : Submodule 𝒪[K] L) :
    Submodule 𝒪[K] L :=
  baseIntegerScalarMulSubmodule K L (chosenIntegerRingUniformizer K ^ n) N


end
end Langlands.NYLL.CyclicCohomology
