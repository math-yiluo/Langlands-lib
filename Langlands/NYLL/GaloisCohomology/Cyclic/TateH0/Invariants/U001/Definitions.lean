/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RepresentationTheory.Invariants
import Mathlib.FieldTheory.Galois.Basic

/-!
# Invariant units

Modified by Worker 5454: extract M094.001 `CyclicCohomology.unitsInvariantSubmodule`
from the pinned NYLL `Nyll/GaloisCohomology/Cyclic/TateH0/Invariants.lean`
(lines 17–24) and prefix the namespace with `Langlands.NYLL`. The source's two
Mathlib imports are kept. The construction is unchanged; the later private
base-unit comparison and the equivalences of the source module are not part
of this unit. See the paired Markdown and `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.CyclicCohomology

noncomputable section

/-- The actual invariant submodule of the unit representation `Lˣ` under `Gal(L/K)`. -/
def unitsInvariantSubmodule (K L : Type) [Field K] [Field L] [Algebra K L] :
    Submodule ℤ (Additive Lˣ) :=
  (Rep.ofAlgebraAutOnUnits K L).ρ.invariants

end

end Langlands.NYLL.CyclicCohomology
