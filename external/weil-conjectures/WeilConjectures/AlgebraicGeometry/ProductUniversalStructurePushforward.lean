/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Fiber
public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# Universal structure pushforward for a product family

Source: Stacks Project, Tag 0BF3, the hypotheses for applying Tag 0BF2 to the product.
(blueprint: lem-sc-product-universal-structure-pushforward).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

private theorem isIso_tensorUnit_iff_app {A B : Scheme.{u}} (a : A ⟶ B) :
    IsIso ((Classical.choose (Modules.exists_tensorPullbackAdjunction a)).unit.app
      (SheafOfModules.unit B.ringCatSheaf)) ↔ ∀ U : B.Opens, IsIso (a.app U) := by
  let adj := Classical.choose (Modules.exists_tensorPullbackAdjunction a)
  let adj' := Modules.pullbackPushforwardAdjunction a
  let e := adj.leftAdjointUniq adj'
  let c := SheafOfModules.unitToPushforwardObjUnit a.toRingCatSheafHom
  have hc : adj'.unit.app (SheafOfModules.unit B.ringCatSheaf) ≫
      (Modules.pushforward a).map (Modules.pullbackObjUnitIso a).hom = c := by
    exact (adj'.homEquiv_unit _ _ (Modules.pullbackObjUnitIso a).hom).symm.trans
      (SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit
        a.toRingCatSheafHom)
  have he : adj.unit.app (SheafOfModules.unit B.ringCatSheaf) ≫
      (Modules.pushforward a).map (e.hom.app _) = adj'.unit.app _ :=
    adj.unit_leftAdjointUniq_hom_app adj' _
  have hiff : IsIso (adj.unit.app (SheafOfModules.unit B.ringCatSheaf)) ↔ IsIso c := by
    rw [← hc, ← he]
    simp only [isIso_comp_right_iff]
  rw [hiff]
  constructor
  · intro h U
    let : IsIso c := h
    have : IsIso (c.val.app (Opposite.op U)) :=
      (SheafOfModules.evaluation B.ringCatSheaf (Opposite.op U)).map_isIso c
    exact (ConcreteCategory.isIso_iff_bijective (a.app U)).mpr
      ((ConcreteCategory.isIso_iff_bijective (c.val.app (Opposite.op U))).mp
        inferInstance)
  · intro h
    have hi : ∀ V : B.Opensᵒᵖ, IsIso (c.val.app V) := by
      intro V
      let : IsIso (a.app V.unop) := h V.unop
      exact (ConcreteCategory.isIso_iff_bijective _).mpr
        ((ConcreteCategory.isIso_iff_bijective (a.app V.unop)).mp inferInstance)
    let : ∀ V, IsIso (c.val.app V) := hi
    let eC : (SheafOfModules.unit B.ringCatSheaf).val ≅
        ((Modules.pushforward a).obj (SheafOfModules.unit A.ringCatSheaf)).val :=
      PresheafOfModules.isoMk (fun V ↦ asIso (c.val.app V))
        (fun {_ _} h ↦ c.val.naturality h)
    have heC : eC.hom = c.val := by ext; rfl
    have : IsIso c.val := heC ▸ (inferInstance : IsIso eC.hom)
    have : IsIso ((SheafOfModules.forget.{u} B.ringCatSheaf).map c) :=
      ‹IsIso c.val›
    exact isIso_of_reflects_iso c (SheafOfModules.forget.{u} B.ringCatSheaf)

/-- Universal structure pushforward is preserved by fibre products of families.
Source: Stacks Project, Tags 0BDP and 0BF3, product-family application of Tag 0BF2.
(blueprint: lem-sc-product-universal-structure-pushforward).

Proof: first compare the tensor-pullback unit with the ordinary pullback unit by
uniqueness of left adjoints. Compose it with the direct image of the canonical
pullback-of-unit isomorphism. The resulting map is the structure map on modules,
whose component on every open U is a.app U on the underlying ring elements. Since
isomorphisms of module sheaves are detected componentwise, the original unit is an
isomorphism exactly when every a.app U is an isomorphism of rings.
For T → S, factor the product over T through T ×_S X. Its first map is the base
change of Y → S along T ×_S X → S, and its second map is the base change of X → S,
up to pullback symmetry. The hypotheses make all open-section ring maps of these
two morphisms isomorphisms. Pullback pasting identifies their composite with the
chosen product-family map, up to a scheme isomorphism. Composition of the ring maps
therefore proves the desired criterion, and hence the tensor-pullback unit assertion.
No flatness or finiteness is used. -/
theorem product_universal_structure_pushforward
    {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (hX : ∀ {T : Scheme.{u}} (t : T ⟶ S),
      IsIso ((Classical.choose
        (Modules.exists_tensorPullbackAdjunction (pullback.snd f t))).unit.app
          (SheafOfModules.unit T.ringCatSheaf)))
    (hY : ∀ {T : Scheme.{u}} (t : T ⟶ S),
      IsIso ((Classical.choose
        (Modules.exists_tensorPullbackAdjunction (pullback.snd g t))).unit.app
          (SheafOfModules.unit T.ringCatSheaf))) :
    ∀ {T : Scheme.{u}} (t : T ⟶ S),
      IsIso ((Classical.choose
        (Modules.exists_tensorPullbackAdjunction
          (pullback.snd (pullback.fst f g ≫ f) t))).unit.app
            (SheafOfModules.unit T.ringCatSheaf)) := by
  intro T t
  let b := pullback.fst t f
  let a := pullback.snd g (pullback.snd t f ≫ f)
  let e : pullback (pullback.fst f g ≫ f) t ≅
      pullback g (pullback.snd t f ≫ f) :=
    pullbackSymmetry _ _ ≪≫ (pullbackLeftPullbackSndIso t f (pullback.fst f g)).symm ≪≫
      pullbackRightPullbackFstIso f g (pullback.snd t f) ≪≫ pullbackSymmetry _ _
  have hb : ∀ U : T.Opens, IsIso (b.app U) := by
    intro U
    have h := (isIso_tensorUnit_iff_app (pullback.snd f t)).mp (hX t) U
    have he : b = (pullbackSymmetry t f).hom ≫ pullback.snd f t := by
      exact (pullbackSymmetry_hom_comp_snd t f).symm
    rw [he, Hom.comp_app]
    infer_instance
  have ha : ∀ U : (pullback t f).Opens, IsIso (a.app U) :=
    (isIso_tensorUnit_iff_app a).mp (hY (pullback.snd t f ≫ f))
  have he : e.hom ≫ a ≫ b = pullback.snd (pullback.fst f g ≫ f) t := by
    dsimp only [e, a, b, Iso.trans_hom, Iso.symm_hom]
    simp only [Category.assoc, pullbackSymmetry_hom_comp_snd_assoc,
      pullbackRightPullbackFstIso_hom_fst_assoc,
      pullbackLeftPullbackSndIso_inv_fst, pullbackSymmetry_hom_comp_fst]
  apply (isIso_tensorUnit_iff_app _).mpr
  intro U
  rw [← he, Hom.comp_app, Hom.comp_app]
  have := hb U
  have := ha (b ⁻¹ᵁ U)
  infer_instance

end AlgebraicGeometry.Scheme
