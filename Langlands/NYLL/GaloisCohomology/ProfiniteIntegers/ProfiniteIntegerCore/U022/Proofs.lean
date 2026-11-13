/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.GaloisCohomology.ProfiniteIntegers.ProfiniteIntegerCore.Statements

/-!
# Compatibility of NYLL profinite-integer reductions

Modified by Worker 192: extract M008.022 from the pinned NYLL source, prefix
the namespace, use its published Statement as the theorem type, and reference
the published `PortInternal.M008` support names. The source closure proof is
retained. See the paired Markdown and `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.ClassFormation

open PortInternal.M008

/-- Reduction maps commute with reduction along a divisibility relation. -/
theorem zHatReduction_transition {m n : ℕ}
    (hm : 0 < m) (hn : 0 < n) (hmn : m ∣ n) (x : ZHat) :
    zHatReduction_transitionStatement hm hn hmn x := by
  let f : d004 → ZMod m :=
    fun z => ZMod.castHom hmn (ZMod m) (z (d003 n hn))
  let g : d004 → ZMod m :=
    fun z => z (d003 m hm)
  have hfg : Set.EqOn f g (d006 : Set d004) := by
    rintro _ ⟨a, rfl⟩
    exact map_intCast (ZMod.castHom hmn (ZMod m)) a
  have hf : Continuous f :=
    continuous_of_discreteTopology.comp (continuous_apply (d003 n hn))
  have hg : Continuous g :=
    continuous_apply (d003 m hm)
  exact hfg.closure hf hg x.property

end Langlands.NYLL.ClassFormation
