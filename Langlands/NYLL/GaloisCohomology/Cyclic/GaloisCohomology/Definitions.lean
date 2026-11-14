/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RepresentationTheory.Homological.GroupCohomology.FiniteCyclic
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90
import Langlands.NYLL.GaloisCohomology.Cyclic.TateComparison.FiniteCyclic.Definitions

/-!
# Cyclic Tate low-degree boundary: the `H¹ ≅ H⁻¹` comparison

Modified by Worker 5454: extract M112.003 `CyclicCohomology.cyclic_H1_iso_HminusOne`
(lines 46–56) and M112.004 `CyclicCohomology.unitsH1IsoTateHminusOne`
(lines 58–64) from the pinned NYLL
`Nyll/GaloisCohomology/Cyclic/GaloisCohomology.lean` and prefix the namespace
with `Langlands.NYLL`. The source's two Mathlib imports are kept; its NYLL
import is replaced by the published M003 finite-cyclic Tate comparison module,
which supplies `TateCohomology.isoFiniteCyclicNegOne`. The two private
theorems of source lines 30–44 (M112.001 `zpowers_eq_top_of_forall_mem_zpowers`
and M112.002 `isCyclic_of_forall_mem_zpowers`) occur only as the proof of the
local `IsCyclic G` instance in M112.003; their source proofs are inlined there
as local `have` steps instead of separate declarations. The constructions and
parameter telescopes are otherwise unchanged. See the paired Markdown and
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.CyclicCohomology

noncomputable section

open CategoryTheory

/-- Low-degree Tate periodicity in degree one:
for a finite cyclic group, `H¹(G,A)` is canonically isomorphic to mathlib's
degree-minus-one Tate cohomology. -/
noncomputable def cyclic_H1_iso_HminusOne {k G : Type} [CommRing k] [Group G]
    [Fintype G] (A : Rep k G) (g : G)
    (hg : ∀ x : G, x ∈ Subgroup.zpowers g) :
    groupCohomology A 1 ≅ tateCohomology A (-1) := by
  -- Source M112.001 `zpowers_eq_top_of_forall_mem_zpowers g hg`, proof inlined.
  have hzpowers : Subgroup.zpowers g = ⊤ := by
    ext x
    constructor
    · intro _
      exact Subgroup.mem_top x
    · intro _
      exact hg x
  -- Source M112.002 `isCyclic_of_forall_mem_zpowers g hg`, proof inlined.
  have hcyclic : IsCyclic G := by
    rw [isCyclic_iff_exists_zpowers_eq_top]
    exact ⟨g, hzpowers⟩
  letI : IsCyclic G := hcyclic
  letI : CommGroup G := IsCyclic.commGroup (α := G)
  exact Rep.FiniteCyclicGroup.groupCohomologyIsoOdd A g hg 1 (by decide) ≪≫
    (TateCohomology.isoFiniteCyclicNegOne A g hg).symm

/-- The cyclic low-degree comparison for the unit representation. -/
noncomputable def unitsH1IsoTateHminusOne (K L : Type) [Field K] [Field L]
    [Algebra K L] [FiniteDimensional K L] (g : Gal(L/K))
    (hg : ∀ x : Gal(L / K), x ∈ Subgroup.zpowers g) :
    groupCohomology.H1 (Rep.ofAlgebraAutOnUnits K L) ≅
      tateCohomology (Rep.ofAlgebraAutOnUnits K L) (-1) :=
  cyclic_H1_iso_HminusOne (Rep.ofAlgebraAutOnUnits K L) g hg

end

end Langlands.NYLL.CyclicCohomology
