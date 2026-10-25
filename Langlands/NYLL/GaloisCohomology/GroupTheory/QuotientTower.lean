/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Adapted by Worker 22 for Langlands.NYLL from ClassFieldTheory commit
fbd320cd8b1b06487c58227e92eb135794267709. Changes: namespace isolation,
explicit Mathlib name qualification, and module documentation. The original
construction and inverse proofs are retained. See the paired Markdown and
licenses/NYLL/LICENSE and licenses/NYLL/NOTICE.
-/

import Mathlib.GroupTheory.Index

/-!
# Quotients in subgroup towers

This file supplies the type-level equivalences between the quotient of a
subgroup and the corresponding quotient after viewing that subgroup inside a
larger group, and the product decomposition of a quotient along a subgroup
tower. These are equivalences of types and require no normality assumptions.
-/



noncomputable section

universe u

namespace Langlands.NYLL.Subgroup

variable {G : Type u} [Group G]

/-- Viewing `H` inside `K` does not change the quotient of `H` by the
subgroup induced by `M`. -/
def quotientSubgroupOfEquiv {H K M : Subgroup G} (hHK : H ≤ K) :
    (↑(H.subgroupOf K) ⧸ (M.subgroupOf K).subgroupOf (H.subgroupOf K)) ≃
      (↑H ⧸ M.subgroupOf H) where
  toFun := Quotient.map' (_root_.Subgroup.subgroupOfEquivOfLe hHK) (by
    intro x y hxy
    rw [QuotientGroup.leftRel_apply] at hxy ⊢
    exact hxy)
  invFun := Quotient.map' (_root_.Subgroup.subgroupOfEquivOfLe hHK).symm (by
    intro x y hxy
    rw [QuotientGroup.leftRel_apply] at hxy ⊢
    exact hxy)
  left_inv q := by
    refine Quotient.inductionOn' q ?_
    intro x
    change Quotient.map' _ _ (Quotient.map' _ _ (Quotient.mk'' x)) = Quotient.mk'' x
    simpa only [Quotient.map'_mk''] using
      congrArg Quotient.mk'' ((_root_.Subgroup.subgroupOfEquivOfLe hHK).symm_apply_apply x)
  right_inv q := by
    refine Quotient.inductionOn' q ?_
    intro x
    change Quotient.map' _ _ (Quotient.map' _ _ (Quotient.mk'' x)) = Quotient.mk'' x
    simpa only [Quotient.map'_mk''] using
      congrArg Quotient.mk'' ((_root_.Subgroup.subgroupOfEquivOfLe hHK).apply_symm_apply x)

/-- A quotient by the bottom of a subgroup tower is equivalent to the product
of the two successive quotient types. -/
def quotientTowerEquiv {M L K : Subgroup G} (hML : M ≤ L) (hLK : L ≤ K) :
    (K ⧸ M.subgroupOf K) ≃
      (K ⧸ L.subgroupOf K) × (L ⧸ M.subgroupOf L) :=
  (_root_.Subgroup.quotientEquivProdOfLE (_root_.Subgroup.subgroupOf_mono K hML)).trans
    (Equiv.prodCongr (Equiv.refl _) (quotientSubgroupOfEquiv hLK))

end Langlands.NYLL.Subgroup
