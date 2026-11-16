/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.ValuationContinuity.UnramifiedExtension.Proofs
import Langlands.NYLL.GaloisCohomology.Cyclic.NormKernelVanishing.Extension.Definitions

/-!
# Target: the extension subgroup of the degree-`f` unramified extension

Modified by Worker 452: extract the theorem signature M301.008
`extensionSubgroup_unramifiedExtensionOfDegree` from the pinned NYLL
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/ValuationContinuity.lean`
as a Prop-valued Statement definition. Prefix the namespace with
`Langlands.NYLL`, append `Statement` to the name, keep the source universe,
variable declaration, parameters, binder kinds and the source inclusion proof
argument `unramifiedExtensionOfDegree_le D K f hf` (the published proof of
M301.007), and omit the proof. Import only the published M301.007 proof and
the published `CyclicCohomology.extensionSubgroup`.
See the paired Markdown and `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

noncomputable section

open scoped Topology

namespace Langlands.NYLL.ClassFormation

open CyclicCohomology

universe u

section DegreeOnly

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace DegreeData

/--
Target: the identity `extensionSubgroup K.field (unramifiedExtensionOfDegree D K f hf)
(unramifiedExtensionOfDegree_le D K f hf) = unramifiedDegreeKernelWithin D K f hf`.
-/
def extensionSubgroup_unramifiedExtensionOfDegreeStatement (D : DegreeData G)
    [IsTopologicalGroup G] (K : FiniteResidueAbstractField D)
    (f : ℕ) (hf : 0 < f) : Prop :=
  extensionSubgroup K.field (unramifiedExtensionOfDegree D K f hf)
      (unramifiedExtensionOfDegree_le D K f hf) =
    unramifiedDegreeKernelWithin D K f hf

end DegreeData

end DegreeOnly

end Langlands.NYLL.ClassFormation
