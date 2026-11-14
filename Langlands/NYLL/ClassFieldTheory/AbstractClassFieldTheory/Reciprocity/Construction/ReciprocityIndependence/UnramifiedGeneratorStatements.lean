/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Frobenius.NormalizedDegree.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.AbstractExtension.StructuralDefinitions
import Langlands.NYLL.GaloisCohomology.Cyclic.NormKernelVanishing.Extension.Definitions

/-!
# Target: degree-one lifts generate a finite unramified Galois quotient

Modified by Worker 5264: extract the public theorem signature M033.016
`quotient_generator_of_unramified_degree_one` from the pinned NYLL
reciprocity-independence source as a Prop-valued Statement definition.
Prefix the namespace with Langlands.NYLL, append `Statement` to the name, keep
the source universe, variable declaration, parameters and binder kinds, use
focused published imports, omit the unused `open KummerTheory`, silence the
unused-variable linter for the source hypotheses that the conclusion does not
mention, and omit the proof.
See the paired Markdown and licenses/NYLL/LICENSE and NOTICE.
-/

universe u

namespace Langlands.NYLL.ClassFormation

open CyclicCohomology

noncomputable section

section groupTheoreticRefinements

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace DegreeData

-- The source hypotheses `hfinite`, `hUnramified` and `hφ` are used only by the
-- omitted proof; their names are kept.
set_option linter.unusedVariables false in
/-- Target: in a finite unramified Galois extension, the restriction of any
degree-one lift is a generator.  This common form is used both in the universal norm-descent lemma
and in the explicit unramified norm-quotient calculation. -/
def quotient_generator_of_unramified_degree_oneStatement (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hnormal : (extensionSubgroup K.field L hLK).Normal]
    [hfinite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)]
    (hUnramified :
      (DegreeData.AbstractExtension.mk L K.field hLK).IsUnramified D)
    (φ : K.field.toSubgroup)
    (hφ : D.normalizedDegree K φ =
      Multiplicative.ofAdd (1 : ZHat)) : Prop :=
    ∀ x : K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK,
      x ∈ Subgroup.zpowers (QuotientGroup.mk φ)

end DegreeData

end groupTheoreticRefinements

end

end Langlands.NYLL.ClassFormation
