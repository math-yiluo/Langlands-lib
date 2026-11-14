/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 5424 (2026-11-14): extract only the proof of M113.066 from
Nyll/GaloisCohomology/Cyclic/Herbrand/HerbrandLowDegree/Basic.lean (lines 770–790; partition unit
lines 772–792)
at commit fbd320cd8b1b06487c58227e92eb135794267709 into Langlands.NYLL. Import only
the published Basic.Statements module, state the theorem as its closed proposition
`tateNorm_sigmaMinusOne_eq_oneStatement`, and introduce that proposition's eight
binders before the unchanged source proof. The source section variables and
noncomputable section are omitted.
Retained license and notices: licenses/NYLL/LICENSE and licenses/NYLL/NOTICE.
-/

import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.Basic.Statements

/-!
# The norm of a coboundary is trivial (NYLL M113.066)

For a finite group `G`, `σ : G` and `a : A`, `N_G (a^(σ-1)) = 1`.
-/

namespace Langlands.NYLL.CyclicCohomology.ProfiniteCohomology.Herbrand

universe uG uA

/-- The norm of a multiplicative coboundary is trivial. This is the calculation
`N_G(b^(σ-1)) = 1` used in the low-degree cyclic-cohomology exact sequence. -/
theorem tateNorm_sigmaMinusOne_eq_one :
    tateNorm_sigmaMinusOne_eq_oneStatement.{uG, uA} := by
  intro G A _ _ _ _ σ a
  have hshift : (∏ g : G, (g * σ) • a) = ∏ g : G, g • a := by
    exact Fintype.prod_equiv (Equiv.mulRight σ)
      (fun g : G => (g * σ) • a) (fun g : G => g • a) (by intro g; rfl)
  calc
    tateNorm G A (sigmaMinusOne G A σ a) = ∏ g : G, ((g * σ) • a) * (g • a)⁻¹ := by
      unfold tateNorm sigmaMinusOne
      apply Finset.prod_congr rfl
      intro g _hg
      calc
        g • (σ • a * a⁻¹) = g • (σ • a) * g • a⁻¹ :=
          MulDistribMulAction.smul_mul g (σ • a) a⁻¹
        _ = (g * σ) • a * (g • a)⁻¹ := by
          rw [← SemigroupAction.mul_smul, smul_inv']
    _ = (∏ g : G, (g * σ) • a) * ∏ g : G, (g • a)⁻¹ := by
      exact Finset.prod_mul_distrib
    _ = 1 := by
      rw [hshift, Finset.prod_inv_distrib, mul_inv_cancel]

end Langlands.NYLL.CyclicCohomology.ProfiniteCohomology.Herbrand
