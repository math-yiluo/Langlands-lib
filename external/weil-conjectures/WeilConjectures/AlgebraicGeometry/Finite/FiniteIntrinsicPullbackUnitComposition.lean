/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicRealizationTransport
import all WeilConjectures.AlgebraicGeometry.ProEtale.Direct.ProEtaleDirectImageGlobalEvaluation
import WeilConjectures.Mathlib.CategoryTheory.MorphismProperty.OverAdjunction

/-! # Unit sections of composite intrinsic finite pullback

Source: Stacks 00YV, composite adjunctions and inverse image on module sheaves
(blueprint: lem-pur-finite-intrinsic-pullback-unit-composition).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
attribute [local implicit_reducible] AlgebraicGeometry.Scheme.ProEt
  CategoryTheory.MorphismProperty
universe u
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry AlgebraicGeometry.Scheme

section Transport
attribute [-instance] CategoryTheory.catToReflQuiver
variable {C₀ C₁ C₂ D₀ D₁ D₂ : Type*}
  [Category C₀] [Category C₁] [Category C₂]
  [Category D₀] [Category D₁] [Category D₂]

section Definitions
variable {C₁ C₂ C₃ D₁ D₂ D₃ : Type*}
  [Category C₁] [Category C₂] [Category C₃]
  [Category D₁] [Category D₂] [Category D₃]
private def trFunctor (e : C₁ ≌ D₁) (f : C₂ ≌ D₂) (F : C₁ ⥤ C₂) : D₁ ⥤ D₂ :=
  e.inverse ⋙ F ⋙ f.functor

private def trIso (e : C₁ ≌ D₁) (f : C₂ ≌ D₂)
    {F G : C₁ ⥤ C₂} (a : F ≅ G) : trFunctor e f F ≅ trFunctor e f G :=
  isoWhiskerLeft e.inverse (isoWhiskerRight a f.functor)

private def trComp (e : C₁ ≌ D₁) (f : C₂ ≌ D₂) (g : C₃ ≌ D₃)
    (F : C₁ ⥤ C₂) (G : C₂ ⥤ C₃) :
    trFunctor e g (F ⋙ G) ≅ trFunctor e f F ⋙ trFunctor f g G :=
  isoWhiskerLeft e.inverse (isoWhiskerRight
    (isoWhiskerLeft F (f.funInvIdAssoc G).symm) g.functor)

private def trAdj (e : C₁ ≌ D₁) (f : C₂ ≌ D₂)
    {L : C₁ ⥤ C₂} {R : C₂ ⥤ C₁} (adj : L ⊣ R) :
    trFunctor e f L ⊣ trFunctor f e R :=
  (e.symm.toAdjunction.comp adj).comp f.toAdjunction

end Definitions

attribute [local implicit_reducible] trFunctor trIso trComp trAdj

private abbrev trComparison (e₀ : C₀ ≌ D₀) (e₁ : C₁ ≌ D₁) (e₂ : C₂ ≌ D₂)
    {F : C₀ ⥤ C₁} {G : C₁ ⥤ C₂} {FG : C₀ ⥤ C₂} (a : FG ≅ F ⋙ G) :=
  trIso e₀ e₂ a ≪≫ trComp e₀ e₁ e₂ F G

private def untransportRight (e : C₀ ≌ D₀) (f : C₁ ≌ D₁)
    {R : C₁ ⥤ C₀} {R' : D₁ ⥤ D₀} (b : trFunctor f e R ≅ R') :
    R' ⋙ e.inverse ≅ f.inverse ⋙ R :=
  Functor.isoWhiskerRight b.symm e.inverse ≪≫
    Functor.isoWhiskerLeft (f.inverse ⋙ R) e.unitIso.symm

attribute [local implicit_reducible] untransportRight

private theorem tr_hom_formula (e : C₀ ≌ D₀) (f : C₁ ≌ D₁)
    {L : C₀ ⥤ C₁} {R : C₁ ⥤ C₀} (a : L ⊣ R)
    {M : D₀} {N : D₁} (h : (trFunctor e f L).obj M ⟶ N) :
    (trAdj e f a).homEquiv M N h =
      e.counitIso.inv.app M ≫ e.functor.map
        (a.homEquiv _ _ (f.unitIso.hom.app _ ≫ f.inverse.map h)) := by
  rw [trAdj, Adjunction.comp_homEquiv, Adjunction.comp_homEquiv]
  rfl

private theorem tr_hom_normalization (e : C₀ ≌ D₀) (f : C₁ ≌ D₁)
    {L : C₀ ⥤ C₁} {R : C₁ ⥤ C₀} (a : L ⊣ R)
    {R' : D₁ ⥤ D₀} (b : trFunctor f e R ≅ R')
    {M : D₀} {N : D₁} (h : (trFunctor e f L).obj M ⟶ N) :
    e.inverse.map (((trAdj e f a).ofNatIsoRight b).homEquiv M N h) ≫
        (untransportRight e f b).hom.app N =
      a.homEquiv _ _ (f.unitIso.hom.app _ ≫ f.inverse.map h) := by
  rw [Adjunction.homEquiv_ofNatIsoRight_apply, tr_hom_formula]
  simp only [untransportRight, Iso.trans_hom, Iso.symm_hom,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app,
    NatTrans.comp_app, Functor.map_comp, Category.assoc]
  rw [← e.inverse.map_comp_assoc (b.hom.app N), b.hom_inv_id_app,
    e.inverse.map_id, Category.id_comp]
  rw [e.inv_fun_map]
  simp only [Category.assoc]
  rw [← e.unit_app_inverse]
  dsimp only [Functor.comp_obj, Equivalence.unit, Equivalence.unitInv]
  simp only [Iso.hom_inv_id_app_assoc, Iso.hom_inv_id_app]
  exact Category.comp_id _

private theorem tr_comp_hom (e₀ : C₀ ≌ D₀) (e₁ : C₁ ≌ D₁) (e₂ : C₂ ≌ D₂)
    {Lg : C₀ ⥤ C₁} {Rg : C₁ ⥤ C₀} {Lf : C₁ ⥤ C₂} {Rf : C₂ ⥤ C₁}
    (ag : Lg ⊣ Rg) (af : Lf ⊣ Rf)
    {Rg' : D₁ ⥤ D₀} {Rf' : D₂ ⥤ D₁}
    (bg : trFunctor e₁ e₀ Rg ≅ Rg') (bf : trFunctor e₂ e₁ Rf ≅ Rf')
    {M : D₀} {N : D₂}
    (h : ((trFunctor e₀ e₁ Lg) ⋙ trFunctor e₁ e₂ Lf).obj M ⟶ N) :
    e₀.inverse.map ((((trAdj e₀ e₁ ag).ofNatIsoRight bg).comp
        ((trAdj e₁ e₂ af).ofNatIsoRight bf)).homEquiv M N h) ≫
        (untransportRight e₀ e₁ bg).hom.app (Rf'.obj N) ≫
        Rg.map ((untransportRight e₁ e₂ bf).hom.app N) =
      (ag.comp af).homEquiv _ _
        (Lf.map (e₁.unitIso.hom.app (Lg.obj (e₀.inverse.obj M))) ≫
          e₂.unitIso.hom.app _ ≫ e₂.inverse.map h) := by
  rw [Adjunction.comp_homEquiv]
  change e₀.inverse.map (((trAdj e₀ e₁ ag).ofNatIsoRight bg).homEquiv _ _
      (((trAdj e₁ e₂ af).ofNatIsoRight bf).homEquiv _ _ h)) ≫ _ ≫ _ = _
  rw [← Category.assoc, tr_hom_normalization]
  rw [← ag.homEquiv_naturality_right]
  rw [Category.assoc, tr_hom_normalization e₁ e₂ af bf h]
  dsimp only [trFunctor, Functor.comp_obj] at h ⊢
  rw [← af.homEquiv_naturality_left]
  rw [Adjunction.comp_homEquiv]
  rfl

private theorem conjugate_hom
    {C D : Type*} [Category C] [Category D]
    {L L' : C ⥤ D} {R R' : D ⥤ C} (a : L ⊣ R) (a' : L' ⊣ R')
    (k : L' ⟶ L) {M : C} {N : D} (h : L.obj M ⟶ N) :
    a'.homEquiv M N (k.app M ≫ h) =
      a.homEquiv M N h ≫ (conjugateEquiv a a' k).app N := by
  simp only [Adjunction.homEquiv_unit, Functor.map_comp, Category.assoc]
  rw [(conjugateEquiv a a' k).naturality]
  simp only [← Category.assoc]
  rw [unit_conjugateEquiv]

private theorem tr_comp_mate (e₀ : C₀ ≌ D₀) (e₁ : C₁ ≌ D₁) (e₂ : C₂ ≌ D₂)
    {Lg : C₀ ⥤ C₁} {Rg : C₁ ⥤ C₀} {Lf : C₁ ⥤ C₂} {Rf : C₂ ⥤ C₁}
    {Lc : C₀ ⥤ C₂} {Rc : C₂ ⥤ C₀}
    (ag : Lg ⊣ Rg) (af : Lf ⊣ Rf) (ac : Lc ⊣ Rc)
    {Rg' : D₁ ⥤ D₀} {Rf' : D₂ ⥤ D₁} {Rc' : D₂ ⥤ D₀}
    (bg : trFunctor e₁ e₀ Rg ≅ Rg') (bf : trFunctor e₂ e₁ Rf ≅ Rf')
    (bc : trFunctor e₂ e₀ Rc ≅ Rc') (k : Lc ≅ Lg ⋙ Lf) (N : D₂) :
    e₀.inverse.map ((conjugateEquiv
      (((trAdj e₀ e₁ ag).ofNatIsoRight bg).comp
        ((trAdj e₁ e₂ af).ofNatIsoRight bf))
      ((trAdj e₀ e₂ ac).ofNatIsoRight bc)
      (trComparison e₀ e₁ e₂ k).hom).app N) ≫
        (untransportRight e₀ e₂ bc).hom.app N =
      (untransportRight e₀ e₁ bg).hom.app (Rf'.obj N) ≫
        Rg.map ((untransportRight e₁ e₂ bf).hom.app N) ≫
        (conjugateEquiv (ag.comp af) ac k.hom).app (e₂.inverse.obj N) := by
  let as_ := ((trAdj e₀ e₁ ag).ofNatIsoRight bg).comp
    ((trAdj e₁ e₂ af).ofNatIsoRight bf)
  let M := (Rf' ⋙ Rg').obj N
  let h : e₂.functor.obj (Lf.obj (e₁.inverse.obj
      (e₁.functor.obj (Lg.obj (e₀.inverse.obj M))))) ⟶ N := as_.counit.app N
  let t := Lf.map (e₁.unitIso.hom.app (Lg.obj (e₀.inverse.obj M))) ≫
    e₂.unitIso.hom.app _ ≫ e₂.inverse.map h
  have ht := tr_comp_hom e₀ e₁ e₂ ag af bg bf h
  have hh : as_.homEquiv M N h = 𝟙 _ := by
    dsimp only [h]
    rw [← as_.homEquiv_symm_id]
    exact Equiv.apply_symm_apply _ _
  change e₀.inverse.map (as_.homEquiv M N h) ≫ _ ≫ _ =
    (ag.comp af).homEquiv _ _ t at ht
  rw [hh, e₀.inverse.map_id, Category.id_comp] at ht
  have hs := tr_hom_normalization e₀ e₂ ac bc
    ((trComparison e₀ e₁ e₂ k).hom.app M ≫ h)
  rw [conjugate_hom as_ ((trAdj e₀ e₂ ac).ofNatIsoRight bc)
    (trComparison e₀ e₁ e₂ k).hom] at hs
  rw [hh, Category.id_comp] at hs
  have hk : e₂.unitIso.hom.app _ ≫
      e₂.inverse.map ((trComparison e₀ e₁ e₂ k).hom.app M ≫ h) =
        k.hom.app (e₀.inverse.obj M) ≫ t := by
    simp only [trComparison, trIso, trComp, Iso.trans_hom, Iso.symm_hom,
      Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
      Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Equivalence.funInvIdAssoc_inv_app, NatTrans.comp_app,
      Functor.map_comp, Category.assoc]
    dsimp only [Functor.comp_obj, trFunctor, t]
    simp only [Equivalence.unit]
    erw [e₂.unit_naturality_assoc, e₂.unit_naturality_assoc]
  change _ = (ag.comp af).homEquiv _ (e₂.inverse.obj N) t at ht
  rw [hk, conjugate_hom (ag.comp af) ac k.hom, ← ht] at hs
  simpa only [Category.assoc] using hs

end Transport

attribute [local implicit_reducible] trFunctor trIso trComp trAdj untransportRight
  sfIntrinsicTransport sfIntrinsicTransportIso sfIntrinsicTransportComp

private abbrev finiteRightComparison (A : Type u) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  Functor.isoWhiskerLeft (sfIntrinsicModuleEquivalence X A).inverse
      (sfIntrinsicDirectImageComparison f A).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (sfIntrinsicModuleEquivalence X A).counitIso _ ≪≫
    Functor.leftUnitor _

private theorem finite_untransport (A : Type u) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    untransportRight (sfIntrinsicModuleEquivalence Y A)
      (sfIntrinsicModuleEquivalence X A) (finiteRightComparison A f) =
        sectionDirectImageIso A f := by
  apply Iso.ext
  apply NatTrans.ext
  funext M
  simp only [untransportRight, finiteRightComparison, sectionDirectImageIso,
    Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_inv, Functor.isoWhiskerLeft_inv,
    Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app,
    Functor.leftUnitor_inv_app, Functor.rightUnitor_hom_app,
    Functor.map_comp, NatTrans.comp_app,
    Category.id_comp, Category.assoc]
  rfl

private theorem finite_comp_mate (A : Type u) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : proEtaleRingModules X (proEtaleConstantRing X A)) :
    (sfIntrinsicModuleEquivalence Z A).inverse.map
        ((conjugateEquiv
          ((sfIntrinsicConstantModuleAdjunction g A).comp
            (sfIntrinsicConstantModuleAdjunction f A))
          (sfIntrinsicConstantModuleAdjunction (f ≫ g) A)
          (sfIntrinsicPullbackComp A f g).hom).app M) ≫
      (sectionDirectImageIso A (f ≫ g)).hom.app M =
    (sectionDirectImageIso A g).hom.app
        ((proEtaleConstantModuleDirectImage f A).obj M) ≫
      (ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) g).map
        ((sectionDirectImageIso A f).hom.app M) ≫
      (ProEtale.lowerStarComp (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f g).hom.app
        ((sfIntrinsicModuleEquivalence X A).inverse.obj M) := by
  have h := tr_comp_mate (sfIntrinsicModuleEquivalence Z A)
    (sfIntrinsicModuleEquivalence Y A) (sfIntrinsicModuleEquivalence X A)
    (ProEtale.upperStarLowerStarAdjunction
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) g)
    (ProEtale.upperStarLowerStarAdjunction
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f)
    (ProEtale.upperStarLowerStarAdjunction
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) (f ≫ g))
    (finiteRightComparison A g) (finiteRightComparison A f)
    (finiteRightComparison A (f ≫ g))
    (ProEtale.upperStarComp (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f g) M
  rw [ProEtale.conjugateEquiv_upperStarComp_hom] at h
  simp only [finite_untransport] at h
  convert h using 1
  congr 2

private theorem intrinsic_compositor_sections
    (A : Type u) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : proEtaleRingModules X (proEtaleConstantRing X A)) (V : Z.ProEt)
    (x : ((proEtaleConstantModuleDirectImage f A ⋙
      proEtaleConstantModuleDirectImage g A).obj M).val.obj (Opposite.op V)) :
    ((conjugateEquiv
      ((sfIntrinsicConstantModuleAdjunction g A).comp
        (sfIntrinsicConstantModuleAdjunction f A))
      (sfIntrinsicConstantModuleAdjunction (f ≫ g) A)
      (sfIntrinsicPullbackComp A f g).hom).app M).val.app (Opposite.op V) x =
        M.val.map ((MorphismProperty.Over.pullbackComp f g).hom.app V).op x := by
  obtain ⟨y, hy⟩ := (sectionRealization_bijective A Z
      ((proEtaleConstantModuleDirectImage g A).obj
        ((proEtaleConstantModuleDirectImage f A).obj M)) (Opposite.op V)).surjective x
  have hm := finite_comp_mate A f g M
  have hv := congrArg (fun t ↦ sectionRealization A X M
      (Opposite.op ((proEtaleBaseChange (f ≫ g)).obj V))
        ((t.hom.app (Opposite.op V)) y)) hm
  change sectionRealization A X M (Opposite.op ((proEtaleBaseChange (f ≫ g)).obj V))
        (((sectionDirectImageIso A (f ≫ g)).hom.app M).hom.app (Opposite.op V)
          (((sfIntrinsicModuleEquivalence Z A).inverse.map
            ((conjugateEquiv
          ((sfIntrinsicConstantModuleAdjunction g A).comp
            (sfIntrinsicConstantModuleAdjunction f A))
          (sfIntrinsicConstantModuleAdjunction (f ≫ g) A)
          (sfIntrinsicPullbackComp A f g).hom).app M)).hom.app (Opposite.op V) y)) =
      sectionRealization A X M (Opposite.op ((proEtaleBaseChange (f ≫ g)).obj V))
        (((sfIntrinsicModuleEquivalence X A).inverse.obj M).obj.map
          ((MorphismProperty.Over.pullbackComp f g).hom.app V).op
          (((sectionDirectImageIso A f).hom.app M).hom.app
            (Opposite.op ((proEtaleBaseChange g).obj V))
            (((sectionDirectImageIso A g).hom.app
              ((proEtaleConstantModuleDirectImage f A).obj M)).hom.app (Opposite.op V) y)))
      at hv
  erw [sectionDirectImageIso_normalization, sectionRealization_naturality,
      sectionRealization_restrict, sectionDirectImageIso_normalization,
      sectionDirectImageIso_normalization, hy] at hv
  exact hv

attribute [local implicit_reducible] proEtaleConstantModuleDirectImage
  proEtaleRingModuleDirectImage SheafOfModules.pushforward
  PresheafOfModules.pushforward PresheafOfModules.pushforward₀
  PresheafOfModules.pushforward₀Obj PresheafOfModules.restrictScalars
  PresheafOfModules.restrictScalarsObj ModuleCat.restrictScalars
  ModuleCat.RestrictScalars.obj'

namespace AlgebraicGeometry.Scheme

/-- The intrinsic pullback compositor sends one adjunction-unit section to the
successive unit sections, with the canonical fibre-product identification.
Source: Stacks 00YV, composite adjunctions and inverse images on module sheaves
(blueprint: lem-pur-finite-intrinsic-pullback-unit-composition).

Proof: conjugation of the pullback compositor is the direct-image comparison.
Transport the ordinary adjunction Hom bijections through the specified module
realization equivalences. Their composite Hom bijection shows that this conjugate
acts on sections by the base-change fibre-product comparison: the realization
unit and counit cancel, and the fixed-scalar conjugate is ordinary precomposition.
The section realization is bijective, so this computation identifies the actual
intrinsic direct-image map. Apply the composite-unit/conjugate identity to a
section and substitute that formula. The composite adjunction unit is the first
unit followed by the second, giving the asserted equation. -/
theorem finiteIntrinsicPullback_unit_comp
    (A : Type u) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (h : Z ⟶ X)
    (M : proEtaleRingModules Y (proEtaleConstantRing Y A)) (U : Y.ProEt)
    (m : M.val.obj (Opposite.op U)) :
    ((sfIntrinsicPullbackComp A h f).hom.app M).val.app
        (Opposite.op ((proEtaleBaseChange (h ≫ f)).obj U))
        (((sfIntrinsicConstantModuleAdjunction (h ≫ f) A).unit.app M).val.app
          (Opposite.op U) m) =
      ((sfIntrinsicPullback A h).obj ((sfIntrinsicPullback A f).obj M)).val.map
        ((MorphismProperty.Over.pullbackComp h f).hom.app U).op
        (((sfIntrinsicConstantModuleAdjunction h A).unit.app
          ((sfIntrinsicPullback A f).obj M)).val.app
            (Opposite.op ((proEtaleBaseChange f).obj U))
            (((sfIntrinsicConstantModuleAdjunction f A).unit.app M).val.app
              (Opposite.op U) m)) := by
  have hu := congrArg (fun t ↦ t.val.app (Opposite.op U) m)
    (unit_conjugateEquiv
      ((sfIntrinsicConstantModuleAdjunction f A).comp
        (sfIntrinsicConstantModuleAdjunction h A))
      (sfIntrinsicConstantModuleAdjunction (h ≫ f) A)
      (sfIntrinsicPullbackComp A h f).hom M)
  change ((conjugateEquiv
      ((sfIntrinsicConstantModuleAdjunction f A).comp
        (sfIntrinsicConstantModuleAdjunction h A))
      (sfIntrinsicConstantModuleAdjunction (h ≫ f) A)
      (sfIntrinsicPullbackComp A h f).hom).app
        ((sfIntrinsicPullback A h).obj ((sfIntrinsicPullback A f).obj M))).val.app
          (Opposite.op U)
          (((sfIntrinsicConstantModuleAdjunction h A).unit.app
            ((sfIntrinsicPullback A f).obj M)).val.app
              (Opposite.op ((proEtaleBaseChange f).obj U))
              (((sfIntrinsicConstantModuleAdjunction f A).unit.app M).val.app
                (Opposite.op U) m)) = _ at hu
  rw [intrinsic_compositor_sections A h f] at hu
  exact hu.symm

end AlgebraicGeometry.Scheme
