/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 5424 (2026-11-14): extract only the proof of M113.068 from
Nyll/GaloisCohomology/Cyclic/Herbrand/HerbrandLowDegree/Basic.lean (lines 799–816; partition unit
lines 801–818)
at commit fbd320cd8b1b06487c58227e92eb135794267709 into Langlands.NYLL. Import only
the published Basic.Statements module, state the theorem as its closed proposition
`smul_tateNorm_eqStatement`, and introduce that proposition's eight binders before
the unchanged source proof. The source section variables and noncomputable
section are omitted.
Retained license and notices: licenses/NYLL/LICENSE and licenses/NYLL/NOTICE.
-/

import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.Basic.Statements

/-!
# The Tate norm is `G`-fixed (NYLL M113.068)

For a finite group `G`, `h : G` and `a : A`, `h • N_G a = N_G a`.
-/

namespace Langlands.NYLL.CyclicCohomology.ProfiniteCohomology.Herbrand

universe uG uA

/-- The norm is fixed by every group element, placing `N_G b` in `A^G` in the
low-degree cyclic-cohomology exact sequence. -/
theorem smul_tateNorm_eq : smul_tateNorm_eqStatement.{uG, uA} := by
  intro G A _ _ _ _ h a
  have hmap : h • (∏ g : G, g • a) = ∏ g : G, h • (g • a) := by
    exact map_prod (MulDistribMulAction.toMonoidHom A h) (fun g : G => g • a) Finset.univ
  have hshift : (∏ g : G, (h * g) • a) = ∏ g : G, g • a := by
    exact Fintype.prod_equiv (Equiv.mulLeft h)
      (fun g : G => (h * g) • a) (fun g : G => g • a) (by intro g; rfl)
  calc
    h • tateNorm G A a = ∏ g : G, h • (g • a) := by
      simpa [tateNorm] using hmap
    _ = ∏ g : G, (h * g) • a := by
      apply Finset.prod_congr rfl
      intro g _hg
      exact (SemigroupAction.mul_smul h g a).symm
    _ = tateNorm G A a := by
      simpa [tateNorm] using hshift

end Langlands.NYLL.CyclicCohomology.ProfiniteCohomology.Herbrand
