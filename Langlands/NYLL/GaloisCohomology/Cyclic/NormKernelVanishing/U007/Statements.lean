/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RepresentationTheory.Homological.TateCohomology.Basic

/-!
# Target for cyclic norm-kernel vanishing

Modified by Worker 120: extract the signature of M004.007 from the pinned
NYLL NormKernelVanishing.lean, prefix its namespace with Langlands.NYLL,
and replace the theorem with a Prop-valued Statement definition. Preserve
the universe-zero telescope and all hypotheses; underscore the unused
generation and vanishing argument names. Use the focused Mathlib import.
See the paired Markdown and licenses/NYLL/LICENSE and NOTICE.
-/

namespace Langlands.NYLL.CyclicCohomology

/-- Target: vanishing of actual Tate H⁻¹ puts every norm-zero vector in
the image of the specified generator minus the identity. -/
def normKernel_le_sigmaMinusOneRange_of_tateHMinusOne_isZeroStatement
    {G : Type} [Group G] [Fintype G]
    (A : Rep.{0} ℤ G) (g : G) (_hg : ∀ x, x ∈ Subgroup.zpowers g)
    (_hzero : CategoryTheory.Limits.IsZero (tateCohomology A (-1))) : Prop :=
  ∀ x : A.V, A.norm.hom x = 0 →
    ∃ y : A.V, A.ρ g y - y = x

end Langlands.NYLL.CyclicCohomology
