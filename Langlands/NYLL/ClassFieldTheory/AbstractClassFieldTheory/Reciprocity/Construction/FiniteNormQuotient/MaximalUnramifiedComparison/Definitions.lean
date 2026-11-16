/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.NormSubgroup.QuotientLift.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FiniteNormQuotient.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FiniteNormQuotient.MaximalUnramifiedIntermediate.Definitions

/-!
# The comparison map from the maximal-unramified to a finite norm quotient

Modified by Worker 5264, 15 November 2026: port the source definition
M039.021 `DegreeData.maximalUnramifiedToFiniteNormQuotient` of
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/FiniteNormQuotient.lean`
at fbd320cd8b1b06487c58227e92eb135794267709. Prefix the namespace with
`Langlands.NYLL`, replace the source imports by the modules of the quotient
lift (M029.035), of the finite norm quotient and of
`fieldAsMaximalUnramifiedIntermediate` (M039.018), and replace
`extensionSubgroup K L hLK` in the finiteness binder by its exact
`Subgroup.subgroupOf` body, as the published finite norm quotient does. The
body passes the private source theorem
`maximalUnramifiedNormSubgroup_le_finiteNormClassHom_ker` (M039.020), whose
proof is not published; it is replaced by that theorem's source proof, in
which the two theorems it applies, M039.012 `finiteNormClass_eq_zero_iff`
and M039.019 `maximalUnramifiedNormSubgroup_le_finiteNormSubgroup` (proofs
not published either), are the local facts `hzero` and `hle` proved by
their source proofs; in `hle` the source rewrite with the `rfl` theorem
M029.025 is replaced by `show`. This is a proof argument, so by proof
irrelevance the definition is the source one. The docstring and the
remaining binders and body are unchanged. Omit the unused `universe u` and
`open CyclicCohomology` and the rest of the source file. See the paired
Markdown and `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.ClassFormation

open KummerTheory

noncomputable section

section quotientMaps

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- The canonical quotient map
`A_K/N_{\widetilde L|K}A_{\widetilde L} → A_K/N_{L|K}A_L`. -/
def maximalUnramifiedToFiniteNormQuotient
    (D : DegreeData G) (A : Rep ℤ G)
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hfinite : Finite (K.toSubgroup ⧸ (L.toSubgroup.subgroupOf K.toSubgroup))] :
    D.MaximalUnramifiedNormQuotient A K L →+
      FiniteNormQuotient A K L hLK :=
  D.maximalUnramifiedNormQuotientLift A K L
    (finiteNormClassHom A K L hLK)
    (by
      intro a ha
      have hzero : finiteNormClass A K L hLK a = 0 ↔
          a ∈ finiteNormSubgroup A K L hLK := by
        unfold finiteNormClass finiteNormClassHom FiniteNormQuotient
        exact QuotientAddGroup.eq_zero_iff _
      have hle : D.maximalUnramifiedNormSubgroup A K L ≤
          finiteNormSubgroup A K L hLK := by
        show infiniteNormSubgroup A (D.maximalUnramifiedField L) K ≤
          finiteNormSubgroup A K L hLK
        rw [infiniteNormSubgroup]
        refine iInf_le_of_le (D.fieldAsMaximalUnramifiedIntermediate K L hLK) ?_
        rfl
      exact hzero.2 (hle ha))

end DegreeData

end quotientMaps

end
end Langlands.NYLL.ClassFormation
