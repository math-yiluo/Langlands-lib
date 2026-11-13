/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RepresentationTheory.Homological.TateCohomology.Basic
import Langlands.NYLL.GaloisCohomology.Cyclic.IntegralRepUniverse

/-!
# NYLL M032.017: fixed vectors are norms when Tate `H⁰` vanishes

Modified by Worker 5424: extract the signature of M032.017 from the pinned
NYLL UnitCohomologyAxiom.lean, prefix its namespace with Langlands.NYLL, and
replace the theorem with a Prop-valued Statement definition. Preserve the
universe-zero telescope and all hypotheses; underscore the unused generation
and vanishing argument names. Use focused imports. See the paired Markdown and
licenses/NYLL/LICENSE and NOTICE.
-/

namespace Langlands.NYLL.ClassFormation

open CategoryTheory

/-- Target: elementwise content of `H⁰(Q,M)=0`: every element fixed by a cyclic
generator is an actual norm. -/
def exists_norm_eq_of_tateHZero_isZeroStatement
    {Q : IntegralRepGroupType} [Group Q] [Fintype Q]
    (M : Rep ℤ Q) (g : Q) (_hg : ∀ x, x ∈ Subgroup.zpowers g)
    (_hzero : Limits.IsZero (tateCohomology M 0)) : Prop :=
  ∀ x : M.V, M.ρ g x = x → ∃ y : M.V, M.norm.hom y = x

end Langlands.NYLL.ClassFormation
