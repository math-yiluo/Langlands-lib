/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Topology.Algebra.Group.Quotient

/-!
# Continuous quotient lift

Modified by Worker 193: extract M014.002 from the pinned NYLL source,
give its private helper the prescribed public internal name, and narrow the
imports to the dependencies of this definition. Retain the source body and
parameter telescope. See the paired Markdown and licenses/NYLL/LICENSE and NOTICE.
-/

namespace Langlands.NYLL.PortInternal.M014

noncomputable section

/-- The continuous lift of a homomorphism through a quotient, used locally
below. -/
def d002
    {A : Type*} {B : Type*} [Group A] [TopologicalSpace A]
    [Group B] [TopologicalSpace B]
    (N : Subgroup A) [N.Normal] (f : A →ₜ* B)
    (hN : N ≤ f.toMonoidHom.ker) : A ⧸ N →ₜ* B := by
  let φ : A ⧸ N →* B := QuotientGroup.lift N f.toMonoidHom hN
  have hcomp : Continuous (fun x : A => φ (QuotientGroup.mk' N x)) := by
    simpa [φ, QuotientGroup.lift_mk'] using f.continuous_toFun
  exact
    { toMonoidHom := φ
      continuous_toFun :=
        (QuotientGroup.isQuotientMap_mk (G := A) (N := N)).continuous_iff.2 hcomp }

end
end Langlands.NYLL.PortInternal.M014
