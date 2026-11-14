/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.FrobeniusLift.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Frobenius.NormalizedDegree.Definitions
import Langlands.NYLL.GaloisCohomology.ProfiniteIntegers.ProfiniteInteger.Divide.U017.Proofs

/-!
# The factorized normalized degree and the Frobenius semigroup

Modified by Worker 5264: extract M012.005 `extensionNormalizedDegree`,
M012.009 `FrobeniusElements` and M012.010 `frobeniusRestriction` from the
pinned NYLL FrobeniusLift source, together with the source-private helper
M012.004 `extensionInertiaWithin_le_normalizedDegree_ker`, which the body of
M012.005 uses. Prefix the namespace with Langlands.NYLL and expand
`extensionSubgroup K.field L hLK` to its exact Mathlib body
`L.toSubgroup.subgroupOf K.field.toSubgroup`, as in the published sibling
module. The source universe and variable declarations, docstrings, binders and
the bodies of M012.005, M012.009 and M012.010 are retained. The helper keeps
its statement, but is proved directly from the published M009.017
`zHatMulNat_zHatDivide` and M009.005 `zHatMulNat_injective` instead of by
rewriting with M011.010 `normalizedDegree_ker`. The source import of the whole
Frobenius module is replaced by the published sibling definitions module, the
published normalized degree definitions and the published M009.017 proof.
See the paired Markdown and licenses/NYLL/LICENSE and NOTICE.
-/

namespace Langlands.NYLL.ClassFormation

noncomputable section

universe u

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace DegreeData

private theorem extensionInertiaWithin_le_normalizedDegree_ker
    (D : DegreeData G) (K : FiniteResidueAbstractField D)
    (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup) :
    D.extensionInertiaWithin K.field L hLK ≤
      (D.normalizedDegree K).toMonoidHom.ker := by
  intro x hx
  have hdeg : D.degree x.1 = 1 := hx.2
  have hnsmul : (K.residueDegree : ℕ) • (D.normalizedDegree K x).toAdd =
      (D.degree x.1).toAdd :=
    zHatMulNat_zHatDivide (K.residueDegree : ℕ) K.residueDegree.property
      (D.restrictedDegreeInMulNatRange K x)
  show D.normalizedDegree K x = 1
  apply Multiplicative.ext
  apply zHatMulNat_injective K.residueDegree.property
  change (K.residueDegree : ℕ) • (D.normalizedDegree K x).toAdd =
    (K.residueDegree : ℕ) • (1 : ZHatMul).toAdd
  rw [hnsmul, hdeg]
  simp only [toAdd_one, nsmul_zero]

/-- The factorized map `d_K : G(\widetilde L|K) → ℤ̂`. -/
def extensionNormalizedDegree (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal] :
    (K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK) →* ZHatMul :=
  QuotientGroup.lift (D.extensionInertiaWithin K.field L hLK)
    (D.normalizedDegree K).toMonoidHom
    (D.extensionInertiaWithin_le_normalizedDegree_ker K L hLK)

/-- The semigroup `Frob(\widetilde L|K)`: elements whose normalized
degree is a strictly positive natural. -/
def FrobeniusElements (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal] : Type u :=
  {σ : K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK //
    ∃ n : ℕ, 0 < n ∧
      D.extensionNormalizedDegree K L hLK σ =
        (Multiplicative.ofAdd (1 : ZHat)) ^ n}

/-- The restriction map occurring in the finite degree-quotient decomposition. -/
def frobeniusRestriction (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal] :
    D.FrobeniusElements K L hLK →
      (K.field.toSubgroup ⧸ L.toSubgroup.subgroupOf K.field.toSubgroup) :=
  fun σ => D.extensionRestriction K.field L hLK σ.1

end DegreeData

end
end Langlands.NYLL.ClassFormation
