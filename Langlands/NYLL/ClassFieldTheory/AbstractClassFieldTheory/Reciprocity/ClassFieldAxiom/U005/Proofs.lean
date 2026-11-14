/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 23 (2026-11-14): extract only the proof of M072.005 from
Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/ClassFieldAxiom.lean
(lines 87–96, docstring 85–86) at commit fbd320cd8b1b06487c58227e92eb135794267709
into Langlands.NYLL; prefix the namespace ClassFormation with Langlands.NYLL;
import only the published Statements module of
Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.ClassFieldAxiom
and state the theorem as that module's `tateHMinusOne_isZeroStatement` applied
to the source binders. The tactic proof begins with a `change` to the source
conclusion. Because the M072.004 proof is not yet in the Library, the source
step `simpa [H] using hcf.tateHMinusOne_card K E` (line 94) is replaced by the
term `(hcf K E).tateHMinusOne_card`, which is the source proof of M072.004
(line 83) inlined. The remaining tactic steps are unchanged. The source
noncomputable section is omitted.
Retained license and notices: licenses/NYLL/LICENSE and licenses/NYLL/NOTICE.
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.ClassFieldAxiom.Statements

/-!
# Vanishing of `Ĥ⁻¹` under the class field axiom (NYLL M072.005)

For a module `A` satisfying the class field axiom, the Tate cohomology group
`Ĥ⁻¹` of the fixed module `A_L` of a finite cyclic subextension `L / K` is a
zero object of `ModuleCat ℤ`.
-/

namespace Langlands.NYLL.ClassFormation

open CyclicCohomology

open CategoryTheory

variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

namespace SatisfiesClassFieldAxiom

variable {A : Rep ℤ G}

/-- The order-one assertion in the class-field axiom gives actual vanishing of
`H⁻¹(G(L/K), A_L)`. -/
theorem tateHMinusOne_isZero
    (hcf : SatisfiesClassFieldAxiom A)
    (K : FiniteAbstractField G) (E : FiniteCyclicSubextension K) :
    tateHMinusOne_isZeroStatement hcf K E := by
  change Limits.IsZero (tateCohomology (E.fixedRepresentation A) (-1))
  let H := tateCohomology (E.fixedRepresentation A) (-1)
  let : Finite H := (hcf K E).finiteTateHMinusOne
  have hcard : Nat.card H = 1 := (hcf K E).tateHMinusOne_card
  let : Subsingleton H := (Nat.card_eq_one_iff_unique.mp hcard).1
  exact ModuleCat.isZero_of_subsingleton H

end SatisfiesClassFieldAxiom

end Langlands.NYLL.ClassFormation
