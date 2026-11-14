/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modified by Worker 516 on 2026-11-14: ported M144.015 to the
Langlands.NYLL namespace and proved the published Statement target.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice.U015.Statements

namespace Langlands.NYLL.CyclicCohomology

noncomputable section

universe u
open scoped ValuativeRel
open LocalFieldTheory

variable (K L : Type u) [Field K] [Field L] [Algebra K L]
  [ValuativeRel K]
  [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-- Membership in a chosen uniformizer-power submodule is scalar-image membership. -/
@[simp]
theorem mem_chosenBaseUniformizerPowSubmodule_iff
    (n : Nat) (N : Submodule 𝒪[K] L) (x : L) :
    mem_chosenBaseUniformizerPowSubmodule_iffStatement K L n N x := Iff.rfl

end
end Langlands.NYLL.CyclicCohomology
