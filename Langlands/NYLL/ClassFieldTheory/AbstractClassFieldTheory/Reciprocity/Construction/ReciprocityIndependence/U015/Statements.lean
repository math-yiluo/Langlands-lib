/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteGaloisSubextension.Statements

/-!
# NYLL finite extensions between finite intermediate fields

Modified by Worker 353, 14 November 2026: extract M033.015 from
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/ReciprocityIndependence.lean`,
lines 247–269 at commit `fbd320cd8b1b06487c58227e92eb135794267709`.
Prefix the namespace with `Langlands.NYLL`, turn the theorem into a
Prop-valued alias of the published M040.025 target, and replace
`extensionSubgroup` by its exact Mathlib body in the telescope.
Preserve the complete source telescope, including the name `hPfinite`.
See the paired Markdown for the full modification record and
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` for retained attribution.
-/

universe u

namespace Langlands.NYLL.ClassFormation

noncomputable section

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace FiniteIntermediateField

/-- If `P | K` is finite and `P` contains the intermediate field `M`, then
`P | M` is finite. -/
def finite_extension_of_leStatement
    {P M K : ClosedSubgroup G}
    (hPK : P.toSubgroup ≤ K.toSubgroup)
    (hMK : M.toSubgroup ≤ K.toSubgroup)
    (hPM : P.toSubgroup ≤ M.toSubgroup)
    [hPfinite : Finite
      (K.toSubgroup ⧸ P.toSubgroup.subgroupOf K.toSubgroup)] : Prop :=
  @Langlands.NYLL.ClassFormation.FiniteGaloisSubextension.finite_extension_over_intermediateStatement
    G _ _ P M K hPK hMK hPM hPfinite

end FiniteIntermediateField

end

end Langlands.NYLL.ClassFormation
