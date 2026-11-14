/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 23 (2026-11-14): extract only the proof of M072.004 from
Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/ClassFieldAxiom.lean
(lines 79–83, docstring 77–78) at commit fbd320cd8b1b06487c58227e92eb135794267709
into Langlands.NYLL; prefix the namespace ClassFormation with Langlands.NYLL;
import only the published Statements module of
Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.ClassFieldAxiom
and state the theorem as that module's `tateHMinusOne_cardStatement` applied to
the source binders. The source term proof is unchanged. The source
noncomputable section is omitted.
Retained license and notices: licenses/NYLL/LICENSE and licenses/NYLL/NOTICE.
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.ClassFieldAxiom.Statements

/-!
# The degree-minus-one half of the class field axiom (NYLL M072.004)

For a module `A` satisfying the class field axiom, the Tate cohomology group
`Ĥ⁻¹` of the fixed module `A_L` of a finite cyclic subextension `L / K` has
order one.
-/

namespace Langlands.NYLL.ClassFormation

open CyclicCohomology

open CategoryTheory

variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

namespace SatisfiesClassFieldAxiom

variable {A : Rep ℤ G}

/-- The degree-minus-one half of the class-field axiom for a bundled cyclic
extension. -/
theorem tateHMinusOne_card
    (hcf : SatisfiesClassFieldAxiom A)
    (K : FiniteAbstractField G) (E : FiniteCyclicSubextension K) :
    tateHMinusOne_cardStatement hcf K E :=
  (hcf K E).tateHMinusOne_card

end SatisfiesClassFieldAxiom

end Langlands.NYLL.ClassFormation
