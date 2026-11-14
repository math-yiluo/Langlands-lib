/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.TateComparison.Definitions

/-!
# Short exactness of the equivariant representation complex: target

Modified by Worker 5454: extract the asserted type of M116.005
`CyclicCohomology.ProfiniteCohomology.Herbrand.equivariantShortComplex_shortExact`
from the pinned NYLL
`Nyll/GaloisCohomology/Cyclic/Herbrand/HerbrandLowDegree/TateComparison.lean`
(lines 67–74) as a Prop-valued definition. Prefix the namespace with
`Langlands.NYLL` and append `Statement` to the theorem name. The section
variables of source lines 27–30 that the theorem includes after its
`omit [Fintype G] in` are written as explicit binders in the source order and
binder kinds, followed by the theorem's own parameters. The proof is omitted.
The imports are Mathlib's `ShortComplex.ShortExact` module and the sibling
data module of this port. See the paired Markdown
and `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

open CategoryTheory

namespace Langlands.NYLL.CyclicCohomology.ProfiniteCohomology.Herbrand

noncomputable section

set_option linter.unusedVariables false in
/-- Target: the short complex `equivariantShortComplex i j hi hj hker` is short exact
when `i` is injective and `j` is surjective. -/
def equivariantShortComplex_shortExactStatement
    {G A B C : Type} [Group G] [CommGroup A] [CommGroup B] [CommGroup C]
    [MulDistribMulAction G A] [MulDistribMulAction G B]
    [MulDistribMulAction G C]
    (i : A →* B) (j : B →* C)
    (hi : ∀ (g : G) (a : A), i (g • a) = g • i a)
    (hj : ∀ (g : G) (b : B), j (g • b) = g • j b)
    (hker : ∀ b : B, j b = 1 ↔ ∃ a : A, i a = b)
    (hinj : Function.Injective i) (hsurj : Function.Surjective j) : Prop :=
  (equivariantShortComplex i j hi hj hker).ShortExact

end

end Langlands.NYLL.CyclicCohomology.ProfiniteCohomology.Herbrand
