/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.DiscreteValuationField.Units.Subquotient

/-!
# Principal-unit quotient comparison equivalences

Adapted by Worker 477 from NYLL M120.051 and M120.083 at commit
`fbd320cd8b1b06487c58227e92eb135794267709`. Modifications: add the
`Langlands.NYLL` namespace prefix; import the published subquotient module in
place of the original Mathlib import list; build the source map
`U^m → G ⧸ U^n` (M120.047) and its kernel and range identifications
(M120.049–050) locally inside M120.051 instead of as separate declarations; and
replace the source antitonicity theorem in M120.083 by the structure field
`U.antitone` that it unfolds to.
-/

namespace Langlands.NYLL.LocalFieldTheory

universe u v

open scoped BigOperators

namespace DiscreteValuationField

namespace AntitoneSubgroupFiltration

variable {G : Type u} [Group G] (U : AntitoneSubgroupFiltration G)

set_option linter.unusedVariables false in
/-- The subquotient `U^m/U^n` as the class of `U^m` inside `G/U^n`. -/
noncomputable def principalUnitSubquotientEquivClassInQuotientOfLe
    {m n : ℕ} (hmn : m ≤ n) [(U.principalUnitSubgroup n).Normal] :
    U.principalUnitSubquotient m n ≃*
      U.principalUnitSubgroupClassInQuotient m n :=
  let f : U.principalUnitSubgroup m →* G ⧸ U.principalUnitSubgroup n :=
    (QuotientGroup.mk' (U.principalUnitSubgroup n)).comp
      (U.principalUnitSubgroup m).subtype
  have hker : f.ker =
      (U.principalUnitSubgroup n).subgroupOf (U.principalUnitSubgroup m) := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    change QuotientGroup.mk' (U.principalUnitSubgroup n) (x : G) = 1 ↔ _
    exact QuotientGroup.eq_one_iff (N := U.principalUnitSubgroup n) (x : G)
  have hrange : f.range = U.principalUnitSubgroupClassInQuotient m n := by
    ext q
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨(x : G), x.property, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  (U.principalUnitSubquotientConcreteEquiv m n).trans
    ((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      ((QuotientGroup.quotientKerEquivRange f).trans
        (MulEquiv.subgroupCongr hrange)))

/-- The third-isomorphism equivalence for principal-unit filtration quotients:
`(G / U^n) / (U^m / U^n) ≃ G / U^m` when `m ≤ n`. -/
noncomputable def quotientModuloPrincipalUnitClassEquivQuotientOfLe
    {m n : ℕ} (hmn : m ≤ n)
    [(U.principalUnitSubgroup n).Normal]
    [(U.principalUnitSubgroup m).Normal] :
    (G ⧸ U.principalUnitSubgroup n) ⧸
        U.principalUnitSubgroupClassInQuotient m n ≃*
      G ⧸ U.principalUnitSubgroup m :=
  QuotientGroup.quotientQuotientEquivQuotient
    (U.principalUnitSubgroup n) (U.principalUnitSubgroup m)
    (U.antitone hmn)

/- Source M120.052: on the class of a subgroup representative `x`, the first
equivalence returns the class of `x` in `G ⧸ U^n`. -/
example {m n : ℕ} (hmn : m ≤ n) [(U.principalUnitSubgroup n).Normal]
    (x : U.principalUnitSubgroup m) :
    ((U.principalUnitSubquotientEquivClassInQuotientOfLe hmn
        (U.principalUnitSubquotientMk m n x) :
      U.principalUnitSubgroupClassInQuotient m n) :
      G ⧸ U.principalUnitSubgroup n) =
      QuotientGroup.mk' (U.principalUnitSubgroup n) (x : G) :=
  rfl

/- Source M120.085 on double-quotient representatives: the class of the class
of `x` is sent to the class of `x` in `G ⧸ U^m`. -/
example {m n : ℕ} (hmn : m ≤ n)
    [(U.principalUnitSubgroup n).Normal]
    [(U.principalUnitSubgroup m).Normal] (x : G) :
    U.quotientModuloPrincipalUnitClassEquivQuotientOfLe hmn
        (QuotientGroup.mk' (U.principalUnitSubgroupClassInQuotient m n)
          (QuotientGroup.mk' (U.principalUnitSubgroup n) x)) =
      QuotientGroup.mk' (U.principalUnitSubgroup m) x :=
  rfl

end AntitoneSubgroupFiltration

end DiscreteValuationField

end Langlands.NYLL.LocalFieldTheory
