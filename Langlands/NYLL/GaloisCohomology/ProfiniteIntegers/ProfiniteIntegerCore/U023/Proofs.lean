/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 65, 13 November 2026 UTC:
Extract only the proof of M008.023 from
Nyll/GaloisCohomology/ProfiniteIntegers/ProfiniteIntegerCore.lean
at fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL
namespace prefix and import only the published ProfiniteIntegerCore
Statements module. Prove its closed proposition
denseRange_intCast_zHatStatement, opening PortInternal.M008 so that the
private source names ZHatAmbient, zHatDiagonal and zHatIntegerSubring are
replaced by their published names d004, d005 and d006. The original proof
route and its steps are retained. The original LICENSE and NOTICE are
retained in licenses/NYLL/.
-/

import Langlands.NYLL.GaloisCohomology.ProfiniteIntegers.ProfiniteIntegerCore.Statements

/-!
# Density of the integers in the profinite-integer closure model

The exact proof of the published target: the ordinary integer cast
`Int.castRingHom ZHat` has dense range in the actual closure model `ZHat`.
-/

namespace Langlands.NYLL.ClassFormation

open PortInternal.M008

/-- The ordinary integers have dense image in their profinite completion. -/
theorem denseRange_intCast_zHat : denseRange_intCast_zHatStatement := by
  have hinclusion : DenseRange
      (Set.inclusion (Subring.le_topologicalClosure d006)) := by
    apply (denseRange_inclusion_iff
      (Subring.le_topologicalClosure d006)).2
    change closure (d006 : Set d004) ⊆
      closure (d006 : Set d004)
    exact Set.Subset.rfl
  have hdiagonal : DenseRange d005.rangeRestrict :=
    d005.rangeRestrict_surjective.denseRange
  have hcomp : DenseRange
      (Set.inclusion (Subring.le_topologicalClosure d006) ∘
        d005.rangeRestrict) :=
    hinclusion.comp hdiagonal
      (continuous_inclusion
        (Subring.le_topologicalClosure d006))
  have heq :
      Set.inclusion (Subring.le_topologicalClosure d006) ∘
          d005.rangeRestrict =
        (fun a : ℤ => Int.castRingHom ZHat a) := by
    funext a
    apply Subtype.ext
    funext i
    rfl
  rw [heq] at hcomp
  exact hcomp

end Langlands.NYLL.ClassFormation
