/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 165, 13 November 2026 UTC:
Extract only the proof of M024.008 from
Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/Norm.lean at
fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL
namespace prefix and import only the published Norm Statements module.
State the theorem as the published Statement applied to the source
parameters and unfold that Statement first. Write the relative coset
subgroup as its published Subgroup.subgroupOf body in place of the
source extensionSubgroup. Drop the original
simp only [relativeCosetAction_mk, leftMulCosetEquiv_mk] step, whose
effect the following definitional change already achieves, so the proof
does not depend on the unpublished M024.002 and M024.004 proofs; all
other original steps are retained. Omit the source noncomputable
section, open CyclicCohomology and all other source declarations.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Norm.Statements

/-!
# The relative norm value is fixed by the base subgroup

The exact proof that the coset-sum norm value of a coefficient fixed by `L`
is fixed by every element of the larger closed subgroup `K`.
-/

namespace Langlands.NYLL.ClassFormation

open KummerTheory

variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

/-- The relative norm value is fixed by the base subgroup action. -/
theorem relativeNormValue_fixed
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [Finite (K.toSubgroup ⧸ (L.toSubgroup.subgroupOf K.toSubgroup))]
    (a : ambientFixedAddSubgroup A L) (k : K.toSubgroup) :
    relativeNormValue_fixedStatement A K L hLK a k := by
  unfold relativeNormValue_fixedStatement
  let := Fintype.ofFinite (K.toSubgroup ⧸ (L.toSubgroup.subgroupOf K.toSubgroup))
  have hterm : ∀ q : K.toSubgroup ⧸ (L.toSubgroup.subgroupOf K.toSubgroup),
      A.ρ k.1 (relativeCosetAction A K L hLK a q) =
        relativeCosetAction A K L hLK a
          (leftMulCosetEquiv (L.toSubgroup.subgroupOf K.toSubgroup) k q) := by
    intro q
    refine Quotient.inductionOn' q ?_
    intro x
    change A.ρ k.1 (A.ρ x.1 a.1) = A.ρ (k.1 * x.1) a.1
    rw [map_mul]
    rfl
  rw [relativeNormValue]
  simp_rw [map_sum, hterm]
  exact (leftMulCosetEquiv (L.toSubgroup.subgroupOf K.toSubgroup) k).sum_comp
    (relativeCosetAction A K L hLK a)

end Langlands.NYLL.ClassFormation
