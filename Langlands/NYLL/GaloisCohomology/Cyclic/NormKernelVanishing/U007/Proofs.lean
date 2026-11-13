/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.GaloisCohomology.Cyclic.NormKernelVanishing.U007.Statements
import Langlands.NYLL.GaloisCohomology.Cyclic.NormKernelVanishing.U006.Definitions

/-!
# Proof of cyclic norm-kernel vanishing

Modified by Worker 152: extract the proof of M004.007 from the pinned NYLL
NormKernelVanishing.lean, prefix its namespace with Langlands.NYLL, and
state it as a proof of the published Statement target. Replace the source's
cyclicity helper M004.001 by the Mathlib cyclicity and subgroup-top
equivalences, and use the published M004.006 comparison. See the paired
Markdown and licenses/NYLL/LICENSE and NOTICE.
-/

open CategoryTheory

namespace Langlands.NYLL.CyclicCohomology

/-- Vanishing of actual Tate H⁻¹ puts every norm-zero vector in the image of
the specified generator minus the identity. -/
theorem normKernel_le_sigmaMinusOneRange_of_tateHMinusOne_isZero
    {G : Type} [Group G] [Fintype G]
    (A : Rep.{0} ℤ G) (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g)
    (hzero : Limits.IsZero (tateCohomology A (-1))) :
    normKernel_le_sigmaMinusOneRange_of_tateHMinusOne_isZeroStatement
      A g hg hzero := by
  let : IsCyclic G :=
    isCyclic_iff_exists_zpowers_eq_top.mpr
      ⟨g, (Subgroup.eq_top_iff' _).mpr hg⟩
  let : CommGroup G := IsCyclic.commGroup (α := G)
  have hH1 : Limits.IsZero (groupCohomology.H1 A) :=
    Limits.IsZero.of_iso hzero (finiteCyclicH1IsoTateHMinusOne A g hg)
  let : Subsingleton (groupCohomology.H1 A) :=
    ModuleCat.subsingleton_of_isZero hH1
  intro x hx
  let : Module ℤ A.V := A.hV2
  let x' : LinearMap.ker A.norm.hom.toLinearMap := ⟨x, hx⟩
  have hclass :
      Rep.FiniteCyclicGroup.groupCohomologyπOdd A g hg 1 ⟨0, rfl⟩ x' = 0 :=
    Subsingleton.elim _ _
  rcases (Rep.FiniteCyclicGroup.groupCohomologyπOdd_eq_zero_iff
    A g hg 1 ⟨0, rfl⟩ x').1 hclass with ⟨y, hy⟩
  exact ⟨y, by simpa [Rep.sub_hom] using hy⟩

end Langlands.NYLL.CyclicCohomology
