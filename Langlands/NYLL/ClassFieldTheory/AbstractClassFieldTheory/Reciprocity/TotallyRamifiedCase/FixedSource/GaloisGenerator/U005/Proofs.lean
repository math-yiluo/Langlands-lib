/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.TotallyRamifiedCase.FixedSource.GaloisGenerator.Statements

/-!
# NYLL M084.005: the transported cyclic generator generates

Modified by Worker 756, 16 November 2026: extract the proof of M084.005
`FiniteCyclicSubextension.galoisGenerator_generates` (lines 102–114) of
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/TotallyRamifiedCase/FixedSource.lean`
at `fbd320cd8b1b06487c58227e92eb135794267709`, prefix the namespace with
`Langlands.NYLL`, replace the source imports by the published statement
module, and state the theorem as the published Statement applied to the
source parameter. The proof script is the source's. The paired Markdown
records every modification. See `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE`.
-/

noncomputable section

namespace Langlands.NYLL.ClassFormation.FiniteCyclicSubextension

variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]
variable {K : FiniteAbstractField G}

/-- The transported generator still generates the whole finite Galois
quotient. -/
theorem galoisGenerator_generates (E : FiniteCyclicSubextension K) :
    galoisGenerator_generatesStatement E := by
  intro x
  let e := E.toFiniteGaloisSubextension.extensionQuotientMulEquiv
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (E.generates (e x))
  apply Subgroup.mem_zpowers_iff.mpr
  refine ⟨n, ?_⟩
  apply e.injective
  change e (e.symm E.generator ^ n) = e x
  exact (map_zpow e _ n).trans
    ((congrArg (fun y => y ^ n) (e.apply_symm_apply E.generator)).trans hn)

end Langlands.NYLL.ClassFormation.FiniteCyclicSubextension

end
