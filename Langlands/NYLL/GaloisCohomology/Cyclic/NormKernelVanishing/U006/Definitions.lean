/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RepresentationTheory.Homological.GroupCohomology.FiniteCyclic
import Langlands.NYLL.GaloisCohomology.Cyclic.TateComparison.FiniteCyclic.Definitions

/-!
# Finite-cyclic H¹ and Tate H⁻¹ comparison

Modified by Worker 120: extract M004.006 from the pinned NYLL source,
prefix the namespace with `Langlands.NYLL`, and import the published M003
comparison. Replace the source's cyclicity helper by the existing Mathlib
cyclicity and subgroup-top equivalences. See the paired Markdown and
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

noncomputable section

open CategoryTheory

namespace Langlands.NYLL.CyclicCohomology

/-- For a finite group with specified generator, actual group cohomology in
degree one is isomorphic to actual Tate cohomology in degree minus one. -/
def finiteCyclicH1IsoTateHMinusOne {G : Type} [Group G] [Fintype G]
    (A : Rep.{0} ℤ G) (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    groupCohomology.H1 A ≅ tateCohomology A (-1) := by
  letI : IsCyclic G :=
    isCyclic_iff_exists_zpowers_eq_top.mpr
      ⟨g, (Subgroup.eq_top_iff' _).mpr hg⟩
  letI : CommGroup G := IsCyclic.commGroup (α := G)
  let e :
      groupCohomology.H1 A ≅
        (Rep.FiniteCyclicGroup.subCompNormHom A g).homology := by
    simpa using
      (Rep.FiniteCyclicGroup.groupCohomologyIsoOdd A g hg 1 ⟨0, rfl⟩)
  exact e ≪≫
    (Langlands.NYLL.TateCohomology.isoFiniteCyclicNegOne A g hg).symm

end Langlands.NYLL.CyclicCohomology
