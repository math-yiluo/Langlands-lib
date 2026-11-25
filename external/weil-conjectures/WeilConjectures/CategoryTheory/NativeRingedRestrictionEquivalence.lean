/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.NativeRingedRestrictionHom

/-! # Module equivalence under the canonical induced topology

Source: Stacks 03A0, 03CH, 03DA, 03DG.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe c d vc vd r
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory.NativeRestriction

variable {C : Type c} {D : Type d} [Category.{vc} C] [Category.{vd} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} (e : C ≌ D)
  [e.inverse.IsDenseSubsite K J]
  (R : Sheaf J CommRingCat.{max c d vc vd r})

/-- The module equivalence induced by an equivalence of sites, with its actual
structural ring maps. Source: Stacks 03A0, 03CH, 03DA, 03DG.
(auxiliary; not a blueprint node). -/
def standardModulesEquivalence :
    NativeModules.{max c d vc vd r, c, vc} R ≌
      NativeModules.{max c d vc vd r, d, vd}
        (restrictedCommRing.{d, c, vd, vc, r}
          (K := K) e.inverse R) := by
  let S := NativeRings.{max c d vc vd r, c, vc} R
  let S' := NativeRings.{max c d vc vd r, d, vd}
    (restrictedCommRing.{d, c, vd, vc, r} (K := K) e.inverse R)
  let φ : S ⟶ (e.functor.sheafPushforwardContinuous RingCat J K).obj S' :=
    ⟨Functor.whiskerRight (NatTrans.op e.unitInv) S.obj⟩
  let ψ : S' ⟶ (e.inverse.sheafPushforwardContinuous RingCat K J).obj S := 𝟙 _
  exact (SheafOfModules.pushforwardPushforwardEquivalence.{max c d vc vd r} e φ ψ
    (NatTrans.ext (funext fun U ↦ by
      change S.obj.map (e.inverse.map (e.counit.app U.unop)).op =
        S.obj.map (e.unitInv.app (e.inverse.obj U.unop)).op
      rw [e.unitInv_app_inverse]))
    (NatTrans.ext (funext fun U ↦ by
      change S.obj.map (e.unitInv.app U.unop).op ≫
        (𝟙 _ ≫ S.obj.map (e.unit.app U.unop).op) = 𝟙 _
      rw [Category.id_comp, ← S.obj.map_comp, ← op_comp, e.unitIso.hom_inv_id_app]
      exact S.obj.map_id _))).symm

/-- Direct restriction is an equivalence, by comparison with the structural
pushforward equivalence. Source: Stacks 03A0, 03CH, 03DA, 03DG.
(auxiliary; not a blueprint node).
Proof: the two functors differ only by identity restriction of scalars, whose
canonical natural isomorphism transports the equivalence. -/
theorem restrictModules_isEquivalence :
    (restrictModules.{d, c, vd, vc, r}
      (K := K) e.inverse R).IsEquivalence := by
  let : (SheafOfModules.pushforward.{max c d vc vd r} (F := e.inverse)
      (𝟙 ((e.inverse.sheafPushforwardContinuous RingCat
        (K) J).obj
          (NativeRings.{max c d vc vd r, c, vc} R)))).IsEquivalence :=
    (standardModulesEquivalence.{c, d, vc, vd, r} e R).isEquivalence_functor
  exact Functor.isEquivalence_of_iso
    (restrictModules_standardIso.{d, c, vd, vc, r}
      (K := K) e.inverse R).symm

end CategoryTheory.NativeRestriction
