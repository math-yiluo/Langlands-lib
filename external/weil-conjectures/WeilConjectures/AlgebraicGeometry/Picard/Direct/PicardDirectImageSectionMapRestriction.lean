/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Picard.Direct.PicardDirectImageSectionMap

import WeilConjectures.AlgebraicGeometry.Picard.Direct.PicardDirectImageUnitMorphismPullback
import WeilConjectures.AlgebraicGeometry.PicardAdjunctionSectionEvaluation
import WeilConjectures.AlgebraicGeometry.Picard.Direct.PicardDirectImageUnitMorphismEvaluation

/-! # Compatibility of the fixed section map with restriction

## References

* Stacks Project, Tags 08HY and 0D5S
-/

@[expose] public section
set_option autoImplicit false
universe v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- The actual canonical section map commutes with successive base change.
It asserts an equality of maps and does not assert their bijectivity. -/
theorem picardDirectImageSectionMap_restriction
    [∀ Y : Scheme.{v},
      HasDerivedCategory.{v + 1} (SheafOfModules.{v} (moduleRings Y.toRingedSpace))]
    {X S : Scheme.{v}} (f : X ⟶ S)
    (L : X.Modules) (W : Scheme.{v}) (k : W ⟶ S) :
    let E := (schemeDerivedDirectImage (pullback.snd f k)).obj
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{v} (moduleRings (pullback f k).toRingedSpace)) 0).obj
          ((Modules.tensorPullback (pullback.fst f k)).obj L))
    ∀ {T T' : Scheme.{v}} (i : T' ⟶ T) (t : T ⟶ W) (t' : T' ⟶ W)
        (h : i ≫ t = t')
        (j : pullback f (t' ≫ k) ⟶ pullback f (t ≫ k)),
        ∀ (hj₁ : j ≫ pullback.fst f (t ≫ k) = pullback.fst f (t' ≫ k)),
          j ≫ pullback.snd f (t ≫ k) = pullback.snd f (t' ≫ k) ≫ i →
          let c := (conjugateIsoEquiv
            ((Classical.choose (Modules.exists_tensorPullbackAdjunction
              (pullback.fst f (t ≫ k)))).comp
                (Classical.choose (Modules.exists_tensorPullbackAdjunction j)))
            (Classical.choose (Modules.exists_tensorPullbackAdjunction
              (pullback.fst f (t' ≫ k))))).symm
            (Modules.pushforwardComp j (pullback.fst f (t ≫ k)) ≪≫
              Modules.pushforwardCongr hj₁)
          ∀ ξ : picardDerivedModelSections E t,
            (c.app L).inv.app ⊤
              (((Modules.tensorPullback j).obj
                ((Modules.tensorPullback (pullback.fst f (t ≫ k))).obj L)).presheaf.map
                  (homOfLE j.preimage_top.ge).op
                    (((Classical.choose (Modules.exists_tensorPullbackAdjunction j)).unit.app
                      ((Modules.tensorPullback (pullback.fst f (t ≫ k))).obj L)).val.app
                        (Opposite.op ⊤)
                          (picardDirectImageSectionMap f L W k t ξ))) =
              picardDirectImageSectionMap f L W k t'
                (picardDerivedModelRestriction E i t t' h ξ) := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
  set_option backward.defeqAttrib.useBackward true in
  set_option maxRecDepth 2048 in
    classical
    dsimp only [Scheme.Modules, Scheme.ringCatSheaf] at *
    intro T T' i t t' h j hj₁ hj₂ ξ
    have : IsIso (SheafOfModules.pullbackObjUnitToUnit j.toRingCatSheafHom) := by
      dsimp only [Scheme.ringCatSheaf]
      infer_instance
    let N := (Modules.tensorPullback (pullback.fst f (t ≫ k))).obj L
    let U := SheafOfModules.unit (moduleRings (pullback f (t ≫ k)).toRingedSpace)
    let adj := Classical.choose (Modules.exists_tensorPullbackAdjunction j)
    let adj₀ := Modules.pullbackPushforwardAdjunction j
    let e := (adj.leftAdjointUniq adj₀).app U ≪≫
      asIso (SheafOfModules.pullbackObjUnitToUnit j.toRingCatSheafHom)
    let c := (conjugateIsoEquiv
      ((Classical.choose (Modules.exists_tensorPullbackAdjunction
        (pullback.fst f (t ≫ k)))).comp adj)
      (Classical.choose (Modules.exists_tensorPullbackAdjunction
        (pullback.fst f (t' ≫ k))))).symm
      (Modules.pushforwardComp j (pullback.fst f (t ≫ k)) ≪≫
        Modules.pushforwardCongr hj₁)
    let n := picardDirectImageUnitMorphism f L W k t ξ
    let n' := picardDirectImageUnitMorphism f L W k t'
      (picardDerivedModelRestriction _ i t t' h ξ)
    have he : adj.homEquiv _ _ e.hom =
        SheafOfModules.unitToPushforwardObjUnit j.toRingCatSheafHom := by
      dsimp only [e, Iso.trans_hom, asIso_hom]
      erw [adj.homEquiv_unit, Functor.map_comp, ← Category.assoc,
        Adjunction.unit_leftAdjointUniq_hom_app]
      exact SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit
        j.toRingCatSheafHom
    have hn : e.hom ≫ n' = (Modules.tensorPullback j).map n ≫ (c.app L).inv := by
      simpa only [e, U, adj, adj₀, n, n', c, Iso.app_hom, Iso.trans_hom,
        asIso_hom, Category.assoc] using
        picardDirectImageUnitMorphism_pullback f L W k i t t' h j hj₁ hj₂ ξ
    have hn' : n' = (e.inv ≫ (Modules.tensorPullback j).map n) ≫ (c.app L).inv := by
      have hh := congrArg (fun a ↦ e.inv ≫ a) hn
      simpa only [Category.assoc, Iso.inv_hom_id_assoc] using hh
    have hev := picardAdjunctionSectionEvaluation j (Modules.tensorPullback j) adj e he
      ((Modules.tensorPullback j).obj N) (e.inv ≫ (Modules.tensorPullback j).map n)
    have hh : adj.homEquiv _ _ (e.hom ≫ (e.inv ≫ (Modules.tensorPullback j).map n)) =
        n ≫ adj.unit.app N := by
      rw [Iso.hom_inv_id_assoc, adj.homEquiv_unit]
      exact adj.unit_naturality n
    rw [hh] at hev
    calc
      _ = (c.app L).inv.app ⊤
          (((Modules.tensorPullback j).obj N).presheaf.map (homOfLE j.preimage_top.ge).op
            ((n ≫ adj.unit.app N).val.app (Opposite.op ⊤)
              (1 : Γ(pullback f (t ≫ k), ⊤)))) :=
        congrArg (fun s ↦ (c.app L).inv.app ⊤
          (((Modules.tensorPullback j).obj N).presheaf.map (homOfLE j.preimage_top.ge).op
            ((adj.unit.app N).val.app (Opposite.op ⊤) s)))
          (picardDirectImageUnitMorphism_evaluation f L W k t ξ).symm
      _ = (c.app L).inv.app ⊤
          ((e.inv ≫ (Modules.tensorPullback j).map n).val.app (Opposite.op ⊤)
            (1 : Γ(pullback f (t' ≫ k), ⊤))) :=
        congrArg ((c.app L).inv.app ⊤) hev
      _ = n'.val.app (Opposite.op ⊤) (1 : Γ(pullback f (t' ≫ k), ⊤)) :=
        congrArg (fun a : SheafOfModules.unit
            (moduleRings (pullback f (t' ≫ k)).toRingedSpace) ⟶
            (Modules.tensorPullback (pullback.fst f (t' ≫ k))).obj L ↦
          a.val.app (Opposite.op ⊤) (1 : Γ(pullback f (t' ≫ k), ⊤))) hn'.symm
      _ = _ := picardDirectImageUnitMorphism_evaluation f L W k t'
        (picardDerivedModelRestriction _ i t t' h ξ)

end AlgebraicGeometry.Scheme
