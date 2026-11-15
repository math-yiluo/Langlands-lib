/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.UnramifiedNormQuotient.ValuationHom.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FiniteNormQuotient.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.AbstractExtension.StructuralDefinitions

/-!
# Target: finite norms lie in the kernel of the unramified valuation map

Modified by Worker 5264, 15 November 2026: state the private source theorem
M058.008 `ValuationData.finiteNormSubgroup_le_unramifiedValuationHom_ker` of
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/UnramifiedNormQuotient.lean`
at fbd320cd8b1b06487c58227e92eb135794267709 as the Prop-valued definition
`Langlands.NYLL.PortInternal.M058.d008Statement`, beside the published port
`Langlands.NYLL.PortInternal.M058.d007` of the private source definition
`unramifiedValuationHom`, which replaces `v.unramifiedValuationHom K L hLK`.
Replace the source imports by focused published imports, add a docstring
(the source theorem has none), omit the proof and the rest of the source
file, and turn off the unused-variable linter for the hypothesis
`hUnramified`, which the proposition does not mention. See the paired
Markdown and `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.PortInternal.M058

open ClassFormation

open KummerTheory

open CyclicCohomology

noncomputable section

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]
variable {D : DegreeData G} {A : Rep ℤ G}

set_option linter.unusedVariables false in
/-- Target for the private source theorem
`ValuationData.finiteNormSubgroup_le_unramifiedValuationHom_ker`: for an
unramified finite extension `L | K`, every norm from `A_L` lies in the kernel
of the normalized valuation of `A_K` reduced modulo `[L : K]`. -/
def d008Statement
    (v : ValuationData D A)
    (K : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [Finite (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)]
    (hUnramified :
      (DegreeData.AbstractExtension.mk L K.field hLK).IsUnramified D) : Prop :=
    finiteNormSubgroup A K.field L hLK ≤
      (d007 v K L hLK).ker

end

end Langlands.NYLL.PortInternal.M058
