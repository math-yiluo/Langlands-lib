/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FiniteNormQuotient.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.FiniteExtension.Definitions

/-!
# The finite norm quotient: statement targets

Modified by Worker 96, 14 November 2026: extract the statements of
M039.010, M039.012, M039.013, M039.014, M039.016 and M039.017 from
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/FiniteNormQuotient.lean`
at fbd320cd8b1b06487c58227e92eb135794267709; prefix the namespace with
`Langlands.NYLL`, import the published finite norm quotient data and finite
abstract extensions, replace `extensionSubgroup K L hLK` by its exact
`Subgroup.subgroupOf` body, and publish Prop-valued definitions with the
`Statement` suffix whose binders are the source hypotheses in source order;
the unused-variables linter is disabled for the induction target only, so the
source hypothesis name `h` is kept. The source proofs and the `simp` and
`elab_as_elim` attributes are omitted.
See the paired Markdown and `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.ClassFormation

open KummerTheory

noncomputable section

section finiteNorms

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

/-- Target: finite norm classes commute with natural scalar multiplication. -/
def finiteNormClass_nsmulStatement
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [Finite (K.toSubgroup ⧸ (L.toSubgroup.subgroupOf K.toSubgroup))]
    (n : ℕ) (a : ambientFixedAddSubgroup A K) : Prop :=
    finiteNormClass A K L hLK (n • a) =
      n • finiteNormClass A K L hLK a

/-- Target: a finite norm class vanishes exactly when its representative lies
in the norm subgroup. -/
def finiteNormClass_eq_zero_iffStatement
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [Finite (K.toSubgroup ⧸ (L.toSubgroup.subgroupOf K.toSubgroup))]
    (a : ambientFixedAddSubgroup A K) : Prop :=
    finiteNormClass A K L hLK a = 0 ↔
      a ∈ finiteNormSubgroup A K L hLK

/-- Target: every finite norm-quotient class has an ambient representative. -/
def finiteNormClass_surjectiveStatement
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [Finite (K.toSubgroup ⧸ (L.toSubgroup.subgroupOf K.toSubgroup))] : Prop :=
    Function.Surjective (finiteNormClass A K L hLK)

set_option linter.unusedVariables false in
/-- Target: eliminate a finite norm-quotient class through an ambient
representative. -/
def FiniteNormQuotient.induction_onStatement
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [Finite (K.toSubgroup ⧸ (L.toSubgroup.subgroupOf K.toSubgroup))]
    {motive : FiniteNormQuotient A K L hLK → Prop}
    (q : FiniteNormQuotient A K L hLK)
    (h : ∀ a, motive (finiteNormClass A K L hLK a)) : Prop :=
    motive q

/-- Target: the quotient lift evaluates on a finite norm class by the chosen
representative. -/
def finiteNormQuotientLift_finiteNormClassStatement
    {B : Type*} [AddCommGroup B]
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [Finite (K.toSubgroup ⧸ (L.toSubgroup.subgroupOf K.toSubgroup))]
    (f : ambientFixedAddSubgroup A K →+ B)
    (hf : finiteNormSubgroup A K L hLK ≤ f.ker)
    (a : ambientFixedAddSubgroup A K) : Prop :=
    finiteNormQuotientLift A K L hLK f hf
        (finiteNormClass A K L hLK a) = f a

/-- Target: every class in the finite norm quotient is killed by `[L : K]`.
This is the actual norm identity
`N_{L/K}(a) = [L : K] a` for an element already fixed by `G_K`. -/
def finiteNormQuotient_degree_nsmul_eq_zeroStatement
    (A : Rep ℤ G) (E : DegreeData.FiniteAbstractExtension G)
    (q : FiniteNormQuotient A E.base E.field E.below) : Prop :=
    (E.degree : ℕ) • q = 0

end finiteNorms

end
end Langlands.NYLL.ClassFormation
