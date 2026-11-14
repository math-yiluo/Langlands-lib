/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RepresentationTheory.Homological.GroupCohomology.FiniteCyclic
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90
import Mathlib.RepresentationTheory.Homological.TateCohomology.Basic

/-!
# Hilbert 90 for negative Tate cohomology of units: target

Modified by Worker 5454: extract the asserted type of M112.005
`CyclicCohomology.hilbert90_unitsTateHminusOne_isZero` from the pinned NYLL
`Nyll/GaloisCohomology/Cyclic/GaloisCohomology.lean` (lines 66–73) as a
Prop-valued definition. Prefix the namespace with `Langlands.NYLL`, append
`Statement` to the theorem name, keep every source parameter in order and
binder kind, and omit the proof. The source's two Mathlib imports are kept and
its NYLL import is replaced by Mathlib's Tate cohomology module, which is all
the target needs; the eventual proof will also import the sibling data module
of this port. See the paired Markdown and `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.CyclicCohomology

noncomputable section

open CategoryTheory

set_option linter.unusedVariables false in
/-- Hilbert 90 transported through the cyclic `H¹ ≅ H^{-1}` comparison.
This is low-degree cyclic Tate cohomology for the coefficient group `Lˣ`: the vanishing of
`H¹(G,Lˣ)` gives the vanishing of `H^{-1}(G,Lˣ)`. -/
def hilbert90_unitsTateHminusOne_isZeroStatement (K L : Type) [Field K]
    [Field L] [Algebra K L] [FiniteDimensional K L] (g : Gal(L/K))
    (hg : ∀ x : Gal(L / K), x ∈ Subgroup.zpowers g) : Prop :=
  CategoryTheory.Limits.IsZero
    (tateCohomology (Rep.ofAlgebraAutOnUnits K L) (-1))

end

end Langlands.NYLL.CyclicCohomology
