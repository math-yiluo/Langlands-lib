/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.FiniteResidue.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.AbstractExtension.StructuralDefinitions
import Langlands.NYLL.GaloisCohomology.Cyclic.NormKernelVanishing.Extension.Definitions

/-!
# NYLL M033.017: finite unramified Galois quotients are cyclic

Modified by Worker 483: extract the signature of M033.017 from the pinned
NYLL ReciprocityIndependence.lean, prefix its namespace with Langlands.NYLL,
and replace the theorem with a Prop-valued Statement definition. Preserve the
universe, the full telescope, binder kinds and order and every hypothesis;
underscore the finiteness and unramifiedness argument names that the
conclusion does not mention. Use focused published imports. See the paired
Markdown and licenses/NYLL/LICENSE and NOTICE.
-/

namespace Langlands.NYLL.ClassFormation

open CyclicCohomology

noncomputable section

universe u

section groupTheoreticRefinements

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- Target: a finite unramified Galois quotient is cyclic: some element's
integer powers exhaust it.  This is the cyclicity input needed to use the
finite-cyclic Tate complexes in the unit-cohomology axiom. -/
def exists_quotient_generator_of_unramifiedStatement
    (D : DegreeData G) (K : FiniteResidueAbstractField D)
    (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hnormal : (extensionSubgroup K.field L hLK).Normal]
    [_hfinite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)]
    (_hUnramified :
      (DegreeData.AbstractExtension.mk L K.field hLK).IsUnramified D) : Prop :=
  ∃ g : K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK,
      ∀ x, x ∈ Subgroup.zpowers g

end DegreeData

end groupTheoreticRefinements

end
end Langlands.NYLL.ClassFormation
