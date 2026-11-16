/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.TotallyRamifiedCase.RestrictionCosets.Statements

/-!
# NYLL M080.009: equal restrictions give equal relative coset actions

Modified by Worker 756, 16 November 2026: extract the proof of M080.009
`FiniteGaloisSubextension.relativeCosetAction_eq_of_restriction_eq`
(lines 409–441) of
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/TotallyRamifiedCase/RestrictionCosets.lean`
at `fbd320cd8b1b06487c58227e92eb135794267709`, prefix the namespace with
`Langlands.NYLL`, replace the source import by the published statement
module, and state the theorem as the published Statement applied to the
source parameters. The proof first unfolds the Statement with `change`, and
the source's `simp only [relativeCosetAction_mk, fixedFieldInclusion_coe]`
is replaced by the definitional `change` it performs. The paired Markdown
records every modification. See `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE`.
-/

noncomputable section

namespace Langlands.NYLL.ClassFormation

open KummerTheory
open CyclicCohomology

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

namespace FiniteGaloisSubextension

/-- Equal restrictions induce equal relative coset actions on elements
fixed by the upper field. -/
theorem relativeCosetAction_eq_of_restriction_eq
    (A : Rep ℤ G) (E : DegreeData.AbstractExtension G)
    (M : FiniteGaloisSubextension E.base)
    (hME : M.field.toSubgroup ≤ E.field.toSubgroup)
    [hEnormal :
      (extensionSubgroup E.base E.field E.below).Normal]
    (a : ambientFixedAddSubgroup A E.field)
    (g t : E.base.toSubgroup ⧸
      extensionSubgroup E.base M.field M.below)
    (hres : abstractReciprocityRestriction
        E.base E.field M.field hME E.below g =
      abstractReciprocityRestriction
        E.base E.field M.field hME E.below t) :
    relativeCosetAction_eq_of_restriction_eqStatement
      A E M hME a g t hres := by
  change relativeCosetAction A E.base M.field M.below
      (fixedFieldInclusion A E.field M.field hME a) g =
    relativeCosetAction A E.base M.field M.below
      (fixedFieldInclusion A E.field M.field hME a) t
  refine Quotient.inductionOn₂' g t ?_ hres
  intro x y hxy
  change A.ρ x.1 a.1 = A.ρ y.1 a.1
  have hxyE : x⁻¹ * y ∈ extensionSubgroup E.base E.field E.below :=
    QuotientGroup.eq.mp hxy
  let e : E.field.toSubgroup := ⟨(x⁻¹ * y).1, hxyE⟩
  have hy : y = x * Subgroup.inclusion E.below e := by
    apply Subtype.ext
    simp [e]
  rw [hy]
  change A.ρ x.1 a.1 = A.ρ (x.1 * e.1) a.1
  rw [map_mul]
  change A.ρ x.1 a.1 = A.ρ x.1 (A.ρ e.1 a.1)
  rw [a.2 e]

end FiniteGaloisSubextension

end Langlands.NYLL.ClassFormation
