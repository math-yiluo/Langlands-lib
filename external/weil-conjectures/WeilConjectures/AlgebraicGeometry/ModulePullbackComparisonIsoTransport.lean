/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedModuleBaseChangeMap
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory

/-! # Transport of a module pullback comparison across a scheme isomorphism

Source: Stacks Project, Tags 06YJ, 08HY and 0D5S.
(blueprint: lem-pc-module-pullback-comparison-iso-transport).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory Limits
namespace AlgebraicGeometry

private theorem postcompose_rightKanExtension
    {C D H H' : Type*} [Category C] [Category D] [Category H] [Category H']
    {L : C ⥤ D} {F : C ⥤ H} {LF : D ⥤ H} (ε : L ⋙ LF ⟶ F)
    [LF.IsRightKanExtension ε] (U : H ⥤ H') [U.IsEquivalence] :
    (LF ⋙ U).IsRightKanExtension
      ((Functor.associator _ _ _).inv ≫ Functor.whiskerRight ε U) := by
  let γ : (Functor.whiskeringRight D H H').obj U ⋙
        (Functor.whiskeringLeft C D H').obj L ⟶
      (Functor.whiskeringLeft C D H).obj L ⋙
        (Functor.whiskeringRight C H H').obj U :=
    { app K := (Functor.associator L K U).inv }
  have (K : D ⥤ H) : IsIso (γ.app K) := by
    dsimp [γ]
    infer_instance
  have : IsIso γ := NatIso.isIso_of_isIso_app γ
  have : (Functor.RightExtension.postcompose₂ L F U).IsEquivalence := by
    change (CostructuredArrow.map₂ γ (𝟙 _)).IsEquivalence
    infer_instance
  exact ⟨⟨(IsTerminal.equivOfIso (Functor.RightExtension.postcompose₂ObjMkIso U ε))
    (IsTerminal.isTerminalObj _ _ (LF.isUniversalOfIsRightKanExtension ε))⟩⟩

/-- A comparison on a module transports through an isomorphism over its base.
Source: Stacks Project, Tag 06YJ, left-derived pullback; Tag 0D5S, composition;
Tag 08HY, counit construction.
(blueprint: lem-pc-module-pullback-comparison-iso-transport).

Proof: Direct image along e.hom is an exact equivalence, inverse to tensor
pullback along e.hom. Tensor pullback composition and e.hom followed by p = a
identify e_*(a^*G) with p^*G. The exact equivalence commutes with localization
and with the single functor; these identifications give m, independently of j.
Unpack hc as a left-derived counit epsilon. Postcompose epsilon with the exact
equivalence e_* and the underived composition identification. Postcomposition by
an equivalence preserves the right Kan extension universal property defining a
left-derived functor. Precompose this counit with j.inv to get a witnessing
left-derived counit for Lp^*. Its value at G[0], followed by the single-complex
identification, defines d. Naturality of the single-complex identifications
and j.hom followed by j.inv = identity give U(c) followed by m = j followed by d.
Thus every supplied j works: any automorphism in j is absorbed in the new
witnessing counit. No flatness of G is assumed. The exact-equivalence argument
also covers the zero module and the empty scheme. -/
theorem exists_modulePullbackComparison_iso_transport
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ {Y Z : Scheme.{u}} (a : Y ⟶ Z), (Scheme.Modules.tensorPullback a).Additive]
    {X Y P : Scheme.{u}} (a : Y ⟶ X) (p : P ⟶ X) (e : Y ≅ P)
    (hp : e.hom ≫ p = a)
    (j : derivedPullback a ⋙ schemeDerivedDirectImage e.hom ≅ derivedPullback p)
    (G : X.Modules)
    (c : (derivedPullback a).obj ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj G) ⟶
        (DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj
            ((Scheme.Modules.tensorPullback a).obj G))
    (hc : IsDerivedModulePullbackComparison a G c) :
    let E := (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj G
    let N := (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings P.toRingedSpace)) 0).obj
        ((Scheme.Modules.tensorPullback p).obj G)
    ∃ d : (derivedPullback p).obj E ⟶ N,
      IsDerivedModulePullbackComparison p G d ∧
      ∃ m : (schemeDerivedDirectImage e.hom).obj
          ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj
              ((Scheme.Modules.tensorPullback a).obj G)) ≅ N,
        (schemeDerivedDirectImage e.hom).map c ≫ m.hom = j.hom.app E ≫ d := by
  let : HasDerivedCategory.{w} X.Modules := inferInstanceAs
    (HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace)))
  let : HasDerivedCategory.{w} Y.Modules := inferInstanceAs
    (HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace)))
  let : HasDerivedCategory.{w} P.Modules := inferInstanceAs
    (HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings P.toRingedSpace)))
  let e₀ : Y.Modules ≌ P.Modules :=
    CategoryTheory.Equivalence.mk (Scheme.Modules.pushforward e.hom)
      (Scheme.Modules.pushforward e.inv)
      ((Scheme.Modules.pushforwardComp e.hom e.inv ≪≫
        Scheme.Modules.pushforwardCongr e.hom_inv_id ≪≫
        Scheme.Modules.pushforwardId Y).symm)
      (Scheme.Modules.pushforwardComp e.inv e.hom ≪≫
        Scheme.Modules.pushforwardCongr e.inv_hom_id ≪≫
        Scheme.Modules.pushforwardId P)
  let U := schemeDerivedDirectImage e.hom
  let V := RingedSpace.moduleDirectImage e.hom.toLRSHom.toShHom
  have : V.Additive := RingedSpace.moduleDirectImage_additive _
  have hV : V = e₀.functor := rfl
  have : V.IsEquivalence := hV ▸ e₀.isEquivalence_functor
  have : U.IsEquivalence :=
    Functor.isEquivalence_of_iso V.rightDerivedFunctorIsoMapDerivedCategory.symm
  have hpa : e.inv ≫ a = p := by
    rw [← hp, ← Category.assoc, e.inv_hom_id, Category.id_comp]
  obtain ⟨aa⟩ := Scheme.Modules.nonempty_tensorPullbackAdjunction a
  obtain ⟨ap⟩ := Scheme.Modules.nonempty_tensorPullbackAdjunction p
  let k : Scheme.Modules.tensorPullback a ⋙ V ≅ Scheme.Modules.tensorPullback p :=
    ((aa.comp e₀.toAdjunction).ofNatIsoRight
      (Scheme.Modules.pushforwardComp e.inv a ≪≫
        Scheme.Modules.pushforwardCongr hpa)).leftAdjointUniq ap
  let Fa : HomotopyCategory X.Modules (ComplexShape.up ℤ) ⥤
      schemeDerivedCategory.{u, w} Y :=
    (Scheme.Modules.tensorPullback a).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh
  let Fp : HomotopyCategory X.Modules (ComplexShape.up ℤ) ⥤
      schemeDerivedCategory.{u, w} P :=
    (Scheme.Modules.tensorPullback p).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh
  let t : Fa ⋙ U ≅ Fp :=
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (asIso V.rightDerivedFunctorUnit).symm ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (Functor.mapHomotopyCategoryCompIso k (ComplexShape.up ℤ)) _
  obtain ⟨ε, hε, hc⟩ := hc
  let α : DerivedCategory.Qh ⋙ (derivedPullback a ⋙ U) ⟶ Fa ⋙ U :=
    (Functor.associator _ _ _).inv ≫ Functor.whiskerRight ε U
  have : (derivedPullback a).IsRightKanExtension ε := hε.isRightKanExtension
  have : (derivedPullback a ⋙ U).IsRightKanExtension α :=
    postcompose_rightKanExtension ε U
  let εp : DerivedCategory.Qh ⋙ derivedPullback p ⟶ Fp :=
    Functor.whiskerLeft DerivedCategory.Qh j.inv ≫ α ≫ t.hom
  have : (DerivedCategory.Qh (C := X.Modules)).IsLocalization
      (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ)) := inferInstance
  have hεp : (derivedPullback p).IsLeftDerivedFunctor εp
      (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ)) := by
    rw [Functor.isLeftDerivedFunctor_iff_isRightKanExtension]
    apply (Functor.isRightKanExtension_iff_of_iso₂ α εp t j ?_).mp inferInstance
    ext K
    simp [εp]
  let S := (HomotopyCategory.singleFunctor X.Modules 0).obj G
  let ba : Fa.obj S ≅ (DerivedCategory.singleFunctor Y.Modules 0).obj
      ((Scheme.Modules.tensorPullback a).obj G) :=
    DerivedCategory.Qh.mapIso ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).mapIso
      ((HomologicalComplex.singleMapHomologicalComplex
        (Scheme.Modules.tensorPullback a) (ComplexShape.up ℤ) 0).app G))
  let bp : Fp.obj S ≅ (DerivedCategory.singleFunctor P.Modules 0).obj
      ((Scheme.Modules.tensorPullback p).obj G) :=
    DerivedCategory.Qh.mapIso ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).mapIso
      ((HomologicalComplex.singleMapHomologicalComplex
        (Scheme.Modules.tensorPullback p) (ComplexShape.up ℤ) 0).app G))
  let d := εp.app S ≫ bp.hom
  let m := U.mapIso ba.symm ≪≫ t.app S ≪≫ bp
  refine ⟨d, ⟨εp, hεp, rfl⟩, m, ?_⟩
  change U.map c ≫ m.hom = j.hom.app (DerivedCategory.Qh.obj S) ≫ d
  change c = ε.app S ≫ ba.hom at hc
  rw [hc, Functor.map_comp]
  simp only [m, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Category.assoc]
  rw [← U.map_comp_assoc ba.hom ba.inv, ba.hom_inv_id, U.map_id, Category.id_comp]
  simp only [Functor.comp_obj, Iso.app_hom, Category.assoc, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.associator_inv_app, Functor.whiskerRight_app,
    Iso.hom_inv_id_app_assoc, d, εp, α]
  exact (Category.id_comp _).symm

end AlgebraicGeometry
