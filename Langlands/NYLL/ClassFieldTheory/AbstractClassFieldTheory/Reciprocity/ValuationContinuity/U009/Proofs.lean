/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.ValuationContinuity.Statements
import Langlands.NYLL.GaloisCohomology.ProfiniteIntegers.ProfiniteInteger.U008.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Frobenius.NormalizedDegree.U009.Proofs

/-!
# NYLL M301.009: surjectivity of the unramified degree homomorphism

Modified by Worker 226, 16 November 2026, using the focused proof route
supplied by Worker 303: extract M301.009 from the pinned NYLL
ValuationContinuity source, prefix the namespace with Langlands.NYLL,
replace broad imports with the published target and two prerequisite
proof modules, and give the theorem the exact published Statement as
its type. The proof body and complete source telescope are unchanged.
See the paired Markdown and licenses/NYLL/LICENSE and NOTICE.
-/

noncomputable section

namespace Langlands.NYLL.ClassFormation

universe u

section DegreeOnly

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- The specified map is surjective: `Function.Surjective (unramifiedDegreeHom D K f hf)`. -/
theorem unramifiedDegreeHom_surjective (D : DegreeData G)
    (K : FiniteResidueAbstractField D)
    (f : ℕ) (hf : 0 < f) :
    unramifiedDegreeHom_surjectiveStatement D K f hf := by
  intro z
  obtain ⟨w, hw⟩ := zHatReduction_surjective f hf z.toAdd
  obtain ⟨k, hk⟩ :=
    D.normalizedDegree_surjective K (Multiplicative.ofAdd w)
  refine ⟨k, ?_⟩
  apply Multiplicative.ext
  change zHatReduction f hf (D.normalizedDegree K k).toAdd = z.toAdd
  rw [hk]
  exact hw

end DegreeData

end DegreeOnly

end Langlands.NYLL.ClassFormation
