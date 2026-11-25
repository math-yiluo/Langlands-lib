/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Bounded.BoundedConstructibleTowerSupplement
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

import all WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement

/-!
# Scalar extension of a localized inverse-image constant model

Source: Stacks Project, Tags 03EL, 0GMW and 093V
(blueprint: lem-sf-finite-field-local-tensor-model).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

namespace FiniteFieldTensor

open SheafOfModules

set_option backward.isDefEq.respectTransparency false
open scoped ChangeOfRings

-- The tensor adjunction argument from ModulePullbackPushforwardAdjunction,
-- with the independent object and morphism universes of the pro-etale site.
private abbrev ringSheaf {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})]
    (R : Sheaf J CommRingCat.{u + 1}) :=
  (sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R

private noncomputable abbrev restriction
    {D : Type (u + 1)} [Category.{u} D] {K : GrothendieckTopology D}
    [K.HasSheafCompose (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})]
    [HasWeakSheafify K AddCommGrpCat.{u + 1}]
    [K.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
    {A S : Sheaf K CommRingCat.{u + 1}} (c : A ⟶ S) :=
  restrictScalars ((sheafCompose K (forget₂ CommRingCat RingCat)).map c)

section

private local instance finiteFieldTensorRestrictedModule
    {D : Type (u + 1)} [Category.{u} D] {K : GrothendieckTopology D}
    [K.HasSheafCompose (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})]
    {A : Sheaf K CommRingCat.{u + 1}} (M : SheafOfModules.{u + 1} (ringSheaf A))
    {X Y : Dᵒᵖ} (i : X ⟶ Y) :
    Module (A.obj.obj Y)
      ((ModuleCat.restrictScalars ((ringSheaf A).obj.map i).hom).obj (M.val.obj Y)) :=
  inferInstanceAs (Module (A.obj.obj Y) (M.val.obj Y))

private theorem tensorRestriction_tmul
    {D : Type (u + 1)} [Category.{u} D] {K : GrothendieckTopology D}
    [K.HasSheafCompose (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})]
    [HasWeakSheafify K AddCommGrpCat.{u + 1}]
    [K.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
    {A S : Sheaf K CommRingCat.{u + 1}} (c : A ⟶ S) (M : SheafOfModules.{u + 1} (ringSheaf A))
    {X Y : Dᵒᵖ} (i : X ⟶ Y) (s : S.obj.obj X) (m : M.val.obj X) :
    (changeOfRingsPresheaf.{u, u + 1, u + 1} c M).map i (s ⊗ₜ[A.obj.obj X, (c.hom.app X).hom] m) =
      S.obj.map i s ⊗ₜ[A.obj.obj Y, (c.hom.app Y).hom] M.val.map i m :=
  Classical.choose_spec (exists_changeOfRingsMap.{u, u + 1, u + 1} c M i) s m

end

private noncomputable def tensorPresheafFunctor
    {D : Type (u + 1)} [Category.{u} D] {K : GrothendieckTopology D}
    [K.HasSheafCompose (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})]
    [HasWeakSheafify K AddCommGrpCat.{u + 1}]
    [K.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
    {A S : Sheaf K CommRingCat.{u + 1}} (c : A ⟶ S) :
    SheafOfModules.{u + 1} (ringSheaf A) ⥤ PresheafOfModules.{u + 1} (ringSheaf S).obj where
  obj M := changeOfRingsPresheaf.{u, u + 1, u + 1} c M
  map {M N} f :=
    show changeOfRingsPresheaf.{u, u + 1, u + 1} c M ⟶
      changeOfRingsPresheaf.{u, u + 1, u + 1} c N from
    { app := fun W ↦
        (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} (c.hom.app W).hom).map (f.val.app W)
      naturality := changeOfRingsHom_naturality.{u, u + 1, u + 1} c _ f }
  map_id M := by
    ext W : 1
    change (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} (c.hom.app W).hom).map (𝟙 _) = _
    exact (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} (c.hom.app W).hom).map_id _
  map_comp f g := by
    ext W : 1
    exact (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} (c.hom.app W).hom).map_comp _ _

private noncomputable def tensorFunctor
    {D : Type (u + 1)} [Category.{u} D] {K : GrothendieckTopology D}
    [K.HasSheafCompose (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})]
    [HasWeakSheafify K AddCommGrpCat.{u + 1}]
    [K.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
    {A S : Sheaf K CommRingCat.{u + 1}} (c : A ⟶ S) :
    SheafOfModules.{u + 1} (ringSheaf A) ⥤ SheafOfModules.{u + 1} (ringSheaf S) :=
  tensorPresheafFunctor c ⋙ PresheafOfModules.sheafification (𝟙 (ringSheaf S).obj)
private noncomputable def tensorToRestriction
    {D : Type (u + 1)} [Category.{u} D] {K : GrothendieckTopology D}
    [K.HasSheafCompose (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})]
    [HasWeakSheafify K AddCommGrpCat.{u + 1}]
    [K.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
    {A S : Sheaf K CommRingCat.{u + 1}} (c : A ⟶ S)
    (M : SheafOfModules.{u + 1} (ringSheaf A)) (H : SheafOfModules.{u + 1} (ringSheaf S))
    (f : changeOfRingsPresheaf.{u, u + 1, u + 1} c M ⟶ H.val) : M ⟶ (restriction c).obj H where
  val :=
    { app := fun W ↦
        ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.toRestrictScalars.{u + 1, u + 1, u + 1}
        (c.hom.app W).hom (f.app W)
      naturality := by
        intro X Y i
        ext m
        change f.app Y ((1 : S.obj.obj Y) ⊗ₜ[A.obj.obj Y, (c.hom.app Y).hom]
          M.val.map i m) = H.val.map i (f.app X
            ((1 : S.obj.obj X) ⊗ₜ[A.obj.obj X, (c.hom.app X).hom] m))
        have h := PresheafOfModules.naturality_apply f i
          ((1 : S.obj.obj X) ⊗ₜ[A.obj.obj X, (c.hom.app X).hom] m)
        rw [tensorRestriction_tmul, map_one] at h
        exact h }

private noncomputable def restrictionToTensor
    {D : Type (u + 1)} [Category.{u} D] {K : GrothendieckTopology D}
    [K.HasSheafCompose (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})]
    [HasWeakSheafify K AddCommGrpCat.{u + 1}]
    [K.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
    {A S : Sheaf K CommRingCat.{u + 1}} (c : A ⟶ S)
    (M : SheafOfModules.{u + 1} (ringSheaf A)) (H : SheafOfModules.{u + 1} (ringSheaf S))
    (g : M ⟶ (restriction c).obj H) : changeOfRingsPresheaf.{u, u + 1, u + 1} c M ⟶ H.val where
  app W := ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars.{u + 1, u + 1, u + 1}
    (c.hom.app W).hom (g.val.app W)
  naturality := by
    intro X Y i
    apply ModuleCat.ExtendScalars.hom_ext
    intro m
    have h := PresheafOfModules.naturality_apply g.val i m
    change ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars.{u + 1, u + 1, u + 1}
      (c.hom.app Y).hom (g.val.app Y)
        ((changeOfRingsPresheaf.{u, u + 1, u + 1} c M).map i
          ((1 : S.obj.obj X) ⊗ₜ[A.obj.obj X, (c.hom.app X).hom] m)) =
      H.val.map i
        (ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars.{u + 1, u + 1, u + 1}
        (c.hom.app X).hom (g.val.app X)
          ((1 : S.obj.obj X) ⊗ₜ[A.obj.obj X, (c.hom.app X).hom] m))
    rw [tensorRestriction_tmul, map_one]
    have atOne (W : Dᵒᵖ) (n : M.val.obj W) :
        ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars.{u + 1, u + 1, u + 1}
          (c.hom.app W).hom (g.val.app W)
            ((1 : S.obj.obj W) ⊗ₜ[A.obj.obj W, (c.hom.app W).hom] n) = g.val.app W n := by
      exact congrArg (fun f : M.val.obj W ⟶
        (ModuleCat.restrictScalars (c.hom.app W).hom).obj (H.val.obj W) ↦ f n)
        ((ModuleCat.ExtendRestrictScalarsAdj.homEquiv.{u + 1, u + 1, u + 1}
          (c.hom.app W).hom).apply_symm_apply (g.val.app W))
    rw [atOne, atOne]
    exact h

private noncomputable def tensorPresheafHomEquiv
    {D : Type (u + 1)} [Category.{u} D] {K : GrothendieckTopology D}
    [K.HasSheafCompose (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})]
    [HasWeakSheafify K AddCommGrpCat.{u + 1}]
    [K.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
    {A S : Sheaf K CommRingCat.{u + 1}} (c : A ⟶ S)
    (M : SheafOfModules.{u + 1} (ringSheaf A)) (H : SheafOfModules.{u + 1} (ringSheaf S)) :
    (changeOfRingsPresheaf.{u, u + 1, u + 1} c M ⟶ H.val) ≃ (M ⟶ (restriction c).obj H) where
  toFun := tensorToRestriction c M H
  invFun := restrictionToTensor c M H
  left_inv f := by
    ext W : 1
    exact (ModuleCat.ExtendRestrictScalarsAdj.homEquiv.{u + 1, u + 1, u + 1}
      (c.hom.app W).hom).symm_apply_apply (f.app W)
  right_inv g := by
    apply SheafOfModules.hom_ext
    ext W : 1
    exact (ModuleCat.ExtendRestrictScalarsAdj.homEquiv.{u + 1, u + 1, u + 1}
      (c.hom.app W).hom).apply_symm_apply (g.val.app W)

private noncomputable def tensorHomEquiv
    {D : Type (u + 1)} [Category.{u} D] {K : GrothendieckTopology D}
    [K.HasSheafCompose (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})]
    [HasWeakSheafify K AddCommGrpCat.{u + 1}]
    [K.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
    {A S : Sheaf K CommRingCat.{u + 1}} (c : A ⟶ S)
    (M : SheafOfModules.{u + 1} (ringSheaf A)) (H : SheafOfModules.{u + 1} (ringSheaf S)) :
    ((tensorFunctor c).obj M ⟶ H) ≃ (M ⟶ (restriction c).obj H) :=
  ((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf S).obj)).homEquiv _ _).trans
    (tensorPresheafHomEquiv c M H)

private theorem tensorHomEquiv_naturality_left
    {D : Type (u + 1)} [Category.{u} D] {K : GrothendieckTopology D}
    [K.HasSheafCompose (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})]
    [HasWeakSheafify K AddCommGrpCat.{u + 1}]
    [K.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
    {A S : Sheaf K CommRingCat.{u + 1}} (c : A ⟶ S)
    {M N : SheafOfModules.{u + 1} (ringSheaf A)} (a : M ⟶ N)
    (H : SheafOfModules.{u + 1} (ringSheaf S)) (f : (tensorFunctor c).obj N ⟶ H) :
    tensorHomEquiv c M H ((tensorFunctor c).map a ≫ f) =
      a ≫ tensorHomEquiv c N H f := by
  change tensorPresheafHomEquiv c M H
      ((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf S).obj)).homEquiv _ _
        ((PresheafOfModules.sheafification (𝟙 (ringSheaf S).obj)).map
          ((tensorPresheafFunctor c).map a) ≫ f)) = _
  rw [Adjunction.homEquiv_naturality_left]
  ext W m
  change ((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf S).obj)).homEquiv
    (changeOfRingsPresheaf.{u, u + 1, u + 1} c N) H f).app W
      ((ModuleCat.extendScalars.{u + 1, u + 1, u + 1} (c.hom.app W).hom).map (a.val.app W)
        ((1 : S.obj.obj W) ⊗ₜ[A.obj.obj W, (c.hom.app W).hom] m)) = _
  rw [ModuleCat.ExtendScalars.map_tmul]
  rfl

private theorem tensorHomEquiv_naturality_right
    {D : Type (u + 1)} [Category.{u} D] {K : GrothendieckTopology D}
    [K.HasSheafCompose (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})]
    [HasWeakSheafify K AddCommGrpCat.{u + 1}]
    [K.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
    {A S : Sheaf K CommRingCat.{u + 1}} (c : A ⟶ S)
    (M : SheafOfModules.{u + 1} (ringSheaf A))
    {H H' : SheafOfModules.{u + 1} (ringSheaf S)}
    (f : (tensorFunctor c).obj M ⟶ H) (b : H ⟶ H') :
    tensorHomEquiv c M H' (f ≫ b) =
      tensorHomEquiv c M H f ≫ (restriction c).map b := by
  change tensorPresheafHomEquiv c M H'
      ((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf S).obj)).homEquiv _ _
        (f ≫ b)) = _
  rw [Adjunction.homEquiv_naturality_right]
  rfl

private noncomputable def tensorAdjunction
    {D : Type (u + 1)} [Category.{u} D] {K : GrothendieckTopology D}
    [K.HasSheafCompose (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})]
    [HasWeakSheafify K AddCommGrpCat.{u + 1}]
    [K.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
    {A S : Sheaf K CommRingCat.{u + 1}} (c : A ⟶ S) : tensorFunctor c ⊣ restriction c :=
  Adjunction.mkOfHomEquiv
    { homEquiv := tensorHomEquiv c
      homEquiv_naturality_left_symm := by
        intro M N H a g
        apply (tensorHomEquiv c M H).injective
        rw [Equiv.apply_symm_apply, tensorHomEquiv_naturality_left,
          Equiv.apply_symm_apply]
      homEquiv_naturality_right := fun f b ↦ tensorHomEquiv_naturality_right c _ f b }


private noncomputable def overRingMap
    {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
    {A S : Sheaf J CommRingCat.{u + 1}} (a : A ⟶ S) (V : C) :
    A.over V ⟶ S.over V :=
  (J.overPullback CommRingCat.{u + 1} V).map a

private noncomputable def overRestrictionIso
    {C : Type (u + 1)} [Category.{u} C] [HasBinaryProducts C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})]
    {A S : Sheaf J CommRingCat.{u + 1}} (a : A ⟶ S) (V : C) :
    pushforward (SheafOfModules.pushforwardOver (R := ringSheaf S) V) ⋙
        restriction a ≅
      restriction (overRingMap a V) ⋙
        pushforward (SheafOfModules.pushforwardOver (R := ringSheaf A) V) := by
  refine NatIso.ofComponents (fun M ↦
    (SheafOfModules.fullyFaithfulForget _).preimageIso
      (PresheafOfModules.isoMk (fun U ↦ ?_) ?_)) ?_
  · let P := (((pushforward (SheafOfModules.pushforwardOver (R := ringSheaf S) V) ⋙
        restriction a).obj M).val.obj U)
    let Q := (((restriction (overRingMap a V) ⋙
        pushforward (SheafOfModules.pushforwardOver (R := ringSheaf A) V)).obj M).val.obj U)
    change P ≅ Q
    refine (show (P : Type (u + 1)) ≃ₗ[A.obj.obj U] Q from
      { toFun := fun m ↦ m
        invFun := fun m ↦ m
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun r m ↦ ?_ }).toModuleIso
    change S.obj.map (Limits.prod.snd : V ⨯ U.unop ⟶ U.unop).op ((a.hom.app U).hom r) •
        (show M.val.obj ((Over.star V).op.obj U) from m) =
      ((a.hom.app ((Over.forget V).op.obj ((Over.star V).op.obj U))).hom
        (A.obj.map (Limits.prod.snd : V ⨯ U.unop ⟶ U.unop).op r)) •
        (show M.val.obj ((Over.star V).op.obj U) from m)
    exact congrArg (fun b ↦ b •
      (show M.val.obj ((Over.star V).op.obj U) from m))
      (ConcreteCategory.congr_hom
        (a.hom.naturality (Limits.prod.snd : V ⨯ U.unop ⟶ U.unop).op).symm r)
  · intro U W h
    ext m
    rfl
  · intro M N h
    ext U m
    rfl
private noncomputable def overExtensionIso
    {C : Type (u + 1)} [Category.{u} C] [HasBinaryProducts C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})]
    [HasWeakSheafify J AddCommGrpCat.{u + 1}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
    {A S : Sheaf J CommRingCat.{u + 1}} (a : A ⟶ S) (V : C)
    [(J.over V).HasSheafCompose (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})]
    [HasWeakSheafify (J.over V) AddCommGrpCat.{u + 1}]
    [(J.over V).WEqualsLocallyBijective AddCommGrpCat.{u + 1}] :
    tensorFunctor a ⋙ overFunctor (ringSheaf S) V ≅
      overFunctor (ringSheaf A) V ⋙ tensorFunctor (overRingMap a V) :=
  (conjugateIsoEquiv
    ((SheafOfModules.overPushforwardOverAdj (R := ringSheaf A) V).comp
      (tensorAdjunction (overRingMap a V)))
    ((tensorAdjunction a).comp
      (SheafOfModules.overPushforwardOverAdj (R := ringSheaf S) V))).symm
      (overRestrictionIso a V).symm


private def constantPresheaf
    {C : Type (u + 1)} [Category.{u} C] (B : Type (u + 1)) [CommRing B] :
    ModuleCat.{u + 1} B ⥤
      PresheafOfModules.{u + 1} ((Functor.const Cᵒᵖ).obj (RingCat.of B)) where
  obj M := { obj := fun _ ↦ M, map := fun _ ↦ 𝟙 M }
  map h := { app := fun _ ↦ h }

private noncomputable def constantPresheafHomEquiv
    {C : Type (u + 1)} [Category.{u} C] [HasTerminal C]
    (B : Type (u + 1)) [CommRing B] (M : ModuleCat.{u + 1} B)
    (P : PresheafOfModules.{u + 1} ((Functor.const Cᵒᵖ).obj (RingCat.of B))) :
    ((constantPresheaf B).obj M ⟶ P) ≃ (M ⟶ P.obj (op (⊤_ C))) where
  toFun h := h.app _
  invFun h :=
    { app := fun U ↦ h ≫ P.map (terminal.from U.unop).op
      naturality := by
        intro U W a
        ext m
        change P.map (terminal.from W.unop).op (h m) =
          P.map a (P.map (terminal.from U.unop).op (h m))
        rw [← P.map_comp_apply]
        have he : (terminal.from W.unop).op = (terminal.from U.unop).op ≫ a :=
          Subsingleton.elim _ _
        rw [he] }
  left_inv h := by
    ext U m
    have hh := PresheafOfModules.naturality_apply h (terminal.from U.unop).op m
    exact hh.symm
  right_inv h := by
    ext m
    change P.map (terminal.from (⊤_ C)).op (h m) = h m
    have he : terminal.from (⊤_ C) = 𝟙 (⊤_ C) := Subsingleton.elim _ _
    rw [he, op_id]
    exact ConcreteCategory.congr_hom (P.presheaf.map_id _) (h m)

private noncomputable def constantPresheafAdjunction
    {C : Type (u + 1)} [Category.{u} C] [HasTerminal C]
    (B : Type (u + 1)) [CommRing B] :
    constantPresheaf (C := C) B ⊣
      PresheafOfModules.evaluation ((Functor.const Cᵒᵖ).obj (RingCat.of B)) (op (⊤_ C)) :=
  Adjunction.mkOfHomEquiv
    { homEquiv := constantPresheafHomEquiv B
      homEquiv_naturality_left_symm := by intros; ext U m; rfl
      homEquiv_naturality_right := by intros; rfl }

private noncomputable def constantSections
    (Y : Scheme.{u}) (B : Type (u + 1)) [CommRing B] :
    pbcModules Y (adicLisseConstantRing Y B) ⥤ ModuleCat.{u + 1} B :=
  SheafOfModules.forget (adicLisseRing Y B) ⋙
    PresheafOfModules.restrictScalars (adicLisseConstantUnit Y B) ⋙
      PresheafOfModules.evaluation.{u + 1} ((Functor.const Y.ProEtᵒᵖ).obj (RingCat.of B))
        (op (⊤_ Y.ProEt))

private noncomputable def constantAdjunction
    (Y : Scheme.{u}) (B : Type (u + 1)) [CommRing B] :
    adicLisseConstantModules Y B ⊣ constantSections Y B :=
  (constantPresheafAdjunction (C := Y.ProEt) B).comp
    (PresheafOfModules.sheafificationAdjunction.{u + 1} (adicLisseConstantUnit Y B))

private noncomputable def fieldRingMap
    (Y : Scheme.{u}) {k k' : Type u} [Field k] [Field k'] (f : k →+* k') :
    adicLisseConstantRing Y (ULift.{u + 1} k) ⟶
      adicLisseConstantRing Y (ULift.{u + 1} k') :=
  (constantSheaf (ProEt.topology Y) CommRingCat.{u + 1}).map
    (CommRingCat.ofHom (RingHom.ulift.{u + 1, u + 1} f))

private theorem fieldUnit_naturality
    (Y : Scheme.{u}) {k k' : Type u} [Field k] [Field k'] (f : k →+* k') :
    adicLisseConstantUnit Y (ULift.{u + 1} k) ≫
        ((adicLisseForget Y).map (fieldRingMap Y f)).hom =
      Functor.whiskerRight
        ((Functor.const Y.ProEtᵒᵖ).map
          (CommRingCat.ofHom (RingHom.ulift.{u + 1, u + 1} f)))
        (forget₂ CommRingCat RingCat) ≫ adicLisseConstantUnit Y (ULift.{u + 1} k') := by
  ext U b
  exact ConcreteCategory.congr_hom
    (congr_app (toSheafify_naturality (ProEt.topology Y)
      ((Functor.const Y.ProEtᵒᵖ).map
        (CommRingCat.ofHom (RingHom.ulift.{u + 1, u + 1} f)))).symm U) b

private noncomputable def restrictionSectionsIso
    (Y : Scheme.{u}) {k k' : Type u} [Field k] [Field k'] (f : k →+* k') :
    pbcRestrict (fieldRingMap Y f) ⋙ constantSections Y (ULift.{u + 1} k) ≅
      constantSections Y (ULift.{u + 1} k') ⋙
        ModuleCat.restrictScalars.{u + 1} (RingHom.ulift.{u + 1, u + 1} f) := by
  refine NatIso.ofComponents (fun M ↦ ?_) ?_
  · let P := (((pbcRestrict (fieldRingMap Y f) ⋙
        constantSections Y (ULift.{u + 1} k)).obj M))
    let Q := (((constantSections Y (ULift.{u + 1} k') ⋙
        ModuleCat.restrictScalars.{u + 1}
          (RingHom.ulift.{u + 1, u + 1} f)).obj M))
    change P ≅ Q
    refine (show (P : Type (u + 1)) ≃ₗ[ULift.{u + 1} k] Q from
      { toFun := fun m ↦ m
        invFun := fun m ↦ m
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun b m ↦ ?_ }).toModuleIso
    change (((fieldRingMap Y f).hom.app (op (⊤_ Y.ProEt))).hom
        (((adicLisseConstantUnit Y (ULift.{u + 1} k)).app (op (⊤_ Y.ProEt))).hom b)) •
          (show M.val.obj (op (⊤_ Y.ProEt)) from m) =
      (((adicLisseConstantUnit Y (ULift.{u + 1} k')).app (op (⊤_ Y.ProEt))).hom
        ((RingHom.ulift f) b)) •
          (show M.val.obj (op (⊤_ Y.ProEt)) from m)
    exact congrArg (fun a ↦ a • (show M.val.obj (op (⊤_ Y.ProEt)) from m))
      (ConcreteCategory.congr_hom (congr_app (fieldUnit_naturality Y f) (op (⊤_ Y.ProEt))) b)
  · intro M N h
    ext m
    rfl

private noncomputable def constantExtensionIso
    (Y : Scheme.{u}) {k k' : Type u} [Field k] [Field k'] (f : k →+* k') :
    adicLisseConstantModules Y (ULift.{u + 1} k) ⋙ pbcExtend (fieldRingMap Y f) ≅
      ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
        (RingHom.ulift.{u + 1, u + 1} f) ⋙
          adicLisseConstantModules Y (ULift.{u + 1} k') :=
  ((constantAdjunction Y (ULift.{u + 1} k)).comp
    (pbcScalarAdjunction (fieldRingMap Y f))).leftAdjointUniq
      (((ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1}
        (RingHom.ulift.{u + 1, u + 1} f)).comp
          (constantAdjunction Y (ULift.{u + 1} k'))).ofNatIsoRight
            (restrictionSectionsIso Y f).symm)

private noncomputable def pbcTensorIso
    (Y : Scheme.{u}) {A S : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}}
    (a : A ⟶ S) : pbcExtend a ≅ tensorFunctor a :=
  (pbcScalarAdjunction a).leftAdjointUniq (tensorAdjunction a)

end FiniteFieldTensor

private noncomputable def inverseImageRestrictionIso
    {X Y : Scheme.{u}} (g : X ⟶ Y)
    {R S : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}} (a : R ⟶ S) :
    proEtaleRingModuleDirectImage g S
        ((proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj S) (Iso.refl _) ⋙
        pbcRestrict a ≅
      pbcRestrict ((proEtaleSheafInverseImage g CommRingCat.{u + 1}).map a) ⋙
        proEtaleRingModuleDirectImage g R
          ((proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj R) (Iso.refl _) := by
  refine NatIso.ofComponents (fun M ↦
    (SheafOfModules.fullyFaithfulForget _).preimageIso
      (PresheafOfModules.isoMk (fun U ↦ ?_) ?_)) ?_
  · let P := (((proEtaleRingModuleDirectImage g S
        ((proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj S) (Iso.refl _) ⋙
        pbcRestrict a).obj M).val.obj U)
    let Q := (((pbcRestrict ((proEtaleSheafInverseImage g CommRingCat.{u + 1}).map a) ⋙
        proEtaleRingModuleDirectImage g R
          ((proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj R)
          (Iso.refl _)).obj M).val.obj U)
    change P ≅ Q
    refine (show (P : Type (u + 1)) ≃ₗ[R.obj.obj U] Q from
      { toFun := fun m ↦ m
        invFun := fun m ↦ m
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun r m ↦ ?_ }).toModuleIso
    change (((proEtaleRingDirectImageMap g S _ (Iso.refl _)).hom.app U).hom
        ((a.hom.app U).hom r)) •
          (show M.val.obj ((proEtaleBaseChange g).op.obj U) from m) =
      ((((proEtaleSheafInverseImage g CommRingCat.{u + 1}).map a).hom.app
        ((proEtaleBaseChange g).op.obj U)).hom
          (((proEtaleRingDirectImageMap g R _ (Iso.refl _)).hom.app U).hom r)) •
          (show M.val.obj ((proEtaleBaseChange g).op.obj U) from m)
    simp only [proEtaleRingDirectImageMap]
    exact congrArg (fun b ↦ b •
        (show M.val.obj ((proEtaleBaseChange g).op.obj U) from m))
      (ConcreteCategory.congr_hom
        (congrArg (fun b ↦ b.hom.app U)
          ((proEtaleSheafAdjunction g CommRingCat.{u + 1}).unit.naturality a)) r)
  · intro U V h
    ext m
    rfl
  · intro M N h
    ext U m
    rfl

private noncomputable def inverseImageExtensionIso
    {X Y : Scheme.{u}} (g : X ⟶ Y)
    {R S : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}} (a : R ⟶ S) :
    pbcExtend a ⋙ proEtaleModuleInverseImage g S ≅
      proEtaleModuleInverseImage g R ⋙
        pbcExtend ((proEtaleSheafInverseImage g CommRingCat.{u + 1}).map a) :=
  (conjugateIsoEquiv
    ((proEtaleModuleInverseImageAdjunction g R).comp
      (pbcScalarAdjunction ((proEtaleSheafInverseImage g CommRingCat.{u + 1}).map a)))
    ((pbcScalarAdjunction a).comp (proEtaleModuleInverseImageAdjunction g S))).symm
      (inverseImageRestrictionIso g a).symm

/-- Scalar extension carries any given localized inverse-image constant model to the
constant tensor model, over the actual inverse-image target ring.
Source: Stacks Project, Tags 03EL, 0GMW and 093V
(blueprint: lem-sf-finite-field-local-tensor-model).

Proof: extension of scalars is left adjoint to restriction. Naturality of the
ring inverse-image adjunction unit identifies the two composites of restriction
and module direct image. Conjugating this identity gives the scalar-extension /
inverse-image comparison, over the actual inverse-image coefficient sheaves.
On the slice at V, restriction of scalars similarly commutes with direct image
along Over.star V: the scalar equation is naturality along the product projection.
Conjugate this identity using the slice restriction/direct-image adjunction and
the tensor adjunction. Apply the resulting slice scalar-extension functor to the
given local isomorphism. Finally, the constant-module functor is left adjoint to
constant-scalar sections at the terminal site object. Naturality of the constant
ring sheafification unit identifies restriction followed by these sections with
these sections followed by ordinary scalar restriction. Uniqueness of left
adjoints gives extension of a constant module as the constant tensor module.
Compose these comparisons before and after the supplied local isomorphism.
The tensor adjunction used on the slice is constructed sectionwise from the
ordinary tensor/restriction Hom equivalence and module sheafification. Thus all
comparisons are linear for the full target ring sheaf, with the target action on
the scalar factor. No finiteness, cover, immersion or inhabited-object assumption
is used; zero modules and empty schemes or localizing objects are included. -/
theorem finiteFieldScalarExtension_localModel
    (Y : Scheme.{u}) {k k' : Type u} [Field k] [Field k'] (f : k →+* k') :
    ∀ (X : Scheme.{u}) (g : X ⟶ Y)
      (F : pbcModules Y (adicLisseConstantRing Y (ULift.{u + 1} k)))
      (V : X.ProEt) (M : ModuleCat.{u + 1} (ULift.{u + 1} k)),
      Nonempty ((SheafOfModules.overFunctor _ V).obj
        ((proEtaleModuleInverseImage g
          (adicLisseConstantRing Y (ULift.{u + 1} k))).obj F) ≅
        (SheafOfModules.overFunctor _ V).obj
          ((proEtaleModuleInverseImage g
            (adicLisseConstantRing Y (ULift.{u + 1} k))).obj
            ((adicLisseConstantModules Y (ULift.{u + 1} k)).obj M))) →
      Nonempty ((SheafOfModules.overFunctor _ V).obj
        ((proEtaleModuleInverseImage g
          (adicLisseConstantRing Y (ULift.{u + 1} k'))).obj
          ((pbcExtend ((constantSheaf (ProEt.topology Y) CommRingCat.{u + 1}).map
            (CommRingCat.ofHom (RingHom.ulift.{u + 1, u + 1} f)))).obj F)) ≅
        (SheafOfModules.overFunctor _ V).obj
          ((proEtaleModuleInverseImage g
            (adicLisseConstantRing Y (ULift.{u + 1} k'))).obj
            ((adicLisseConstantModules Y (ULift.{u + 1} k')).obj
              ((ModuleCat.extendScalars
                (RingHom.ulift.{u + 1, u + 1} f)).obj M)))) := by
  intro X g F V M h
  obtain ⟨eM⟩ := h
  let R := adicLisseConstantRing Y (ULift.{u + 1} k)
  let S := adicLisseConstantRing Y (ULift.{u + 1} k')
  let a := FiniteFieldTensor.fieldRingMap Y f
  let ax := (proEtaleSheafInverseImage g CommRingCat.{u + 1}).map a
  let LR := proEtaleModuleInverseImage g R
  let LS := proEtaleModuleInverseImage g S
  let OR := SheafOfModules.overFunctor.{u + 1}
    ((sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      ((proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj R)) V
  let OS := SheafOfModules.overFunctor.{u + 1}
    ((sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      ((proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj S)) V
  let E := FiniteFieldTensor.tensorFunctor (FiniteFieldTensor.overRingMap ax V)
  let e : ∀ N : pbcModules Y R,
      OS.obj (LS.obj ((pbcExtend a).obj N)) ≅ E.obj (OR.obj (LR.obj N)) :=
    fun N ↦ OS.mapIso ((inverseImageExtensionIso g a).app N) ≪≫
      OS.mapIso ((FiniteFieldTensor.pbcTensorIso X ax).app (LR.obj N)) ≪≫
        (FiniteFieldTensor.overExtensionIso ax V).app (LR.obj N)
  exact ⟨e F ≪≫ E.mapIso eM ≪≫
    (e ((adicLisseConstantModules Y (ULift.{u + 1} k)).obj M)).symm ≪≫
      OS.mapIso (LS.mapIso ((FiniteFieldTensor.constantExtensionIso Y f).app M))⟩

end AlgebraicGeometry.Scheme
