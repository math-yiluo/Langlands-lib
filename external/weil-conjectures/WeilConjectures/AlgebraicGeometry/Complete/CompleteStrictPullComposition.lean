/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
public import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafChangeAdjunctionSupplement
public import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.CompletedReductionPullbackSquare
public import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.CompletedOrdinaryComparisons
public import WeilConjectures.AlgebraicGeometry.ProEtale.Canonical.ProEtaleCanonicalDerivedPullbackNormalization
public import WeilConjectures.CategoryTheory.DerivedExactSquareComposition
public import WeilConjectures.AlgebraicGeometry.Strict.Tower.StrictTowerExchangeMateNormalization
public import WeilConjectures.AlgebraicGeometry.StrictTower.StrictConstantTowerOperationsSupplement

/-!
# Inverse-image compositors and restriction to constant coefficients

The completed derived inverse-image compositor is the localization of a section-normalized
module compositor, and restriction to constant coefficients respects the module and derived
inverse-image compositors.

Source: Weil conjectures blueprint, node proposition-composition-base-change-rf-shriek--4, proof
step 8; Stacks Tags 06YY and 0D6D (blueprint: proposition-composition-base-change-rf-shriek--4).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

variable {C D E : Type*} [Category C] [Category D] [Category E]
  [Abelian C] [Abelian D] [Abelian E]
  [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
  {F : C ⥤ D} {G : D ⥤ E} {H : C ⥤ E}
  [F.Additive] [G.Additive] [H.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]

/-- The derived compositor induced by an ordinary compositor of exact functors. -/
abbrev mapDerivedCategoryTriangleIso' (σ : H ≅ F ⋙ G) :
    H.mapDerivedCategory ≅ F.mapDerivedCategory ⋙ G.mapDerivedCategory :=
  mapDerivedCategoryNatIso σ ≪≫ (mapDerivedCategoryCompIso F G).symm

/-- The derived compositor is the localization of the ordinary one. -/
theorem mapDerivedCategoryTriangleIso'_hom_app_factors (σ : H ≅ F ⋙ G)
    (K : CochainComplex C ℤ) :
    H.mapDerivedCategoryFactors.hom.app K ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex σ.hom (.up ℤ)).app K) =
      (mapDerivedCategoryTriangleIso' σ).hom.app (DerivedCategory.Q.obj K) ≫
        G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app K) ≫
        G.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj K) := by
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc,
    mapDerivedCategoryCompIso_hom_app_factors, mapDerivedCategoryNatIso_fac]

end CategoryTheory.Functor

namespace AlgebraicGeometry.Scheme

section RestrictionComposition

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
  (RZ SZ : Sheaf (ProEt.topology Z) CommRingCat.{u + 1})
  (RY SY : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
  (RX SX : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
  (aZ : RZ ⟶ SZ) (aY : RY ⟶ SY) (aX : RX ⟶ SX)
  (cRg : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj RZ ≅ RY)
  (cSg : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj SZ ≅ SY)
  (cRf : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj RY ≅ RX)
  (cSf : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj SY ≅ SX)
  (cRfg : (proEtaleSheafInverseImage (f ≫ g) CommRingCat.{u + 1}).obj RZ ≅ RX)
  (cSfg : (proEtaleSheafInverseImage (f ≫ g) CommRingCat.{u + 1}).obj SZ ≅ SX)
  (commg : cRg.hom ≫ aY = (proEtaleSheafInverseImage g CommRingCat.{u + 1}).map aZ ≫ cSg.hom)
  (commf : cRf.hom ≫ aX = (proEtaleSheafInverseImage f CommRingCat.{u + 1}).map aY ≫ cSf.hom)
  (commfg : cRfg.hom ≫ aX =
    (proEtaleSheafInverseImage (f ≫ g) CommRingCat.{u + 1}).map aZ ≫ cSfg.hom)

include commf in
/-- The restriction/pullback comparison is the inverse mate of identity on sections. -/
theorem restrictionPullbackInv_mate :
    mateEquiv (proEtaleRingModuleAdjunction f SY SX cSf)
        (proEtaleRingModuleAdjunction f RY RX cRf)
        (TwoSquare.mk _ _ _ _
          (proEtaleRingRestrictionPullbackInv f RY SY RX SX aY aX cRf cSf commf)) =
      TwoSquare.mk _ _ _ _
        (proEtaleRingRestrictionDirectImage f RY SY RX SX aY aX cRf cSf commf).hom := by
  rw [← Equiv.eq_symm_apply]
  refine NatTrans.ext (funext fun M ↦ ?_)
  simp only [mateEquiv_symm_apply, proEtaleRingRestrictionPullbackInv,
    proEtaleRingRestrictionPullbackApp, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.leftUnitor_inv_app, Functor.rightUnitor_hom_app, Functor.comp_map,
    Category.id_comp]
  simp only [TwoSquare.mk, CategoryTheory.Functor.map_id]
  dsimp only [Functor.comp_obj]
  simp only [Category.id_comp]
  exact (Category.comp_id _).symm



private lemma mateSquare'
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}
    {L₃ L₄ : E ⥤ F} {R₃ R₄ : F ⥤ E}
    {G : C ⥤ E} {H : D ⥤ F}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (a₃ : L₃ ⊣ R₃) (a₄ : L₄ ⊣ R₄)
    (q : TwoSquare G L₁ L₃ H) (r : TwoSquare G L₂ L₄ H)
    (s : L₄ ⟶ L₃) (t : L₂ ⟶ L₁)
    (h : (mateEquiv a₁ a₃ q).whiskerBottom (conjugateEquiv a₃ a₄ s) =
      (mateEquiv a₂ a₄ r).whiskerTop (conjugateEquiv a₁ a₂ t)) :
    q.whiskerRight s = r.whiskerLeft t := by
  apply (mateEquiv a₁ a₄).injective
  rw [mateEquiv_conjugateEquiv_vcomp, conjugateEquiv_mateEquiv_vcomp]
  exact h

include commf commg commfg in
/-- Restriction of scalars respects the inverse-image compositors, when both compositors
are conjugate to the fibre-product pasting maps on sections.
Source: Stacks, Modules on Sites, Tags 03D8 and 03D7 (blueprint:
proposition-composition-base-change-rf-shriek--4).
-/
theorem restrictionPullbackInv_comp
    (κR : proEtaleRingModulePullback (f ≫ g) RZ RX cRfg ≅
      proEtaleRingModulePullback g RZ RY cRg ⋙ proEtaleRingModulePullback f RY RX cRf)
    (κS : proEtaleRingModulePullback (f ≫ g) SZ SX cSfg ≅
      proEtaleRingModulePullback g SZ SY cSg ⋙ proEtaleRingModulePullback f SY SX cSf)
    (hκR : ∀ (N : proEtaleRingModules X RX) (U : Z.ProEt)
      (m : ((proEtaleRingModuleDirectImage f RY RX cRf ⋙
        proEtaleRingModuleDirectImage g RZ RY cRg).obj N).val.obj (Opposite.op U)),
      ((conjugateEquiv ((proEtaleRingModuleAdjunction g RZ RY cRg).comp
          (proEtaleRingModuleAdjunction f RY RX cRf))
          (proEtaleRingModuleAdjunction (f ≫ g) RZ RX cRfg) κR.hom).app N).val.app
            (Opposite.op U) m =
        N.val.map ((MorphismProperty.Over.pullbackComp f g).hom.app U).op m)
    (hκS : ∀ (N : proEtaleRingModules X SX) (U : Z.ProEt)
      (m : ((proEtaleRingModuleDirectImage f SY SX cSf ⋙
        proEtaleRingModuleDirectImage g SZ SY cSg).obj N).val.obj (Opposite.op U)),
      ((conjugateEquiv ((proEtaleRingModuleAdjunction g SZ SY cSg).comp
          (proEtaleRingModuleAdjunction f SY SX cSf))
          (proEtaleRingModuleAdjunction (f ≫ g) SZ SX cSfg) κS.hom).app N).val.app
            (Opposite.op U) m =
        N.val.map ((MorphismProperty.Over.pullbackComp f g).hom.app U).op m)
    (M : proEtaleRingModules Z SZ) :
    κR.hom.app ((proEtaleRingRestrictScalars aZ).obj M) ≫
        (proEtaleRingModulePullback f RY RX cRf).map
          ((proEtaleRingRestrictionPullbackInv g RZ SZ RY SY aZ aY cRg cSg commg).app M) ≫
        (proEtaleRingRestrictionPullbackInv f RY SY RX SX aY aX cRf cSf commf).app
          ((proEtaleRingModulePullback g SZ SY cSg).obj M) =
      (proEtaleRingRestrictionPullbackInv (f ≫ g) RZ SZ RX SX aZ aX cRfg cSfg commfg).app M ≫
        (proEtaleRingRestrictScalars aX).map (κS.hom.app M) := by
  let q := (TwoSquare.mk _ _ _ _
      (proEtaleRingRestrictionPullbackInv g RZ SZ RY SY aZ aY cRg cSg commg)).vComp
    (TwoSquare.mk _ _ _ _
      (proEtaleRingRestrictionPullbackInv f RY SY RX SX aY aX cRf cSf commf))
  have h := mateSquare' ((proEtaleRingModuleAdjunction g SZ SY cSg).comp
      (proEtaleRingModuleAdjunction f SY SX cSf))
    (proEtaleRingModuleAdjunction (f ≫ g) SZ SX cSfg)
    ((proEtaleRingModuleAdjunction g RZ RY cRg).comp
      (proEtaleRingModuleAdjunction f RY RX cRf))
    (proEtaleRingModuleAdjunction (f ≫ g) RZ RX cRfg) q
    (TwoSquare.mk _ _ _ _
      (proEtaleRingRestrictionPullbackInv (f ≫ g) RZ SZ RX SX aZ aX cRfg cSfg commfg))
    κR.hom κS.hom
  have hc : q.whiskerRight κR.hom =
      (TwoSquare.mk _ _ _ _ (proEtaleRingRestrictionPullbackInv (f ≫ g) RZ SZ RX SX
        aZ aX cRfg cSfg commfg)).whiskerLeft κS.hom := by
    apply h
    dsimp only [q]
    rw [mateEquiv_hcomp, restrictionPullbackInv_mate, restrictionPullbackInv_mate,
      restrictionPullbackInv_mate]
    refine NatTrans.ext (funext fun N ↦ ?_)
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro W
    ext n
    simp only [TwoSquare.whiskerBottom, TwoSquare.whiskerTop, TwoSquare.hComp,
      TwoSquare.mk, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
      Category.comp_id, SheafOfModules.comp_val, PresheafOfModules.comp_app]
    simp only [ModuleCat.comp_apply]
    have dirApply {U V : Scheme.{u}} (q : U ⟶ V)
        (RV SV : Sheaf (ProEt.topology V) CommRingCat.{u + 1})
        (RU SU : Sheaf (ProEt.topology U) CommRingCat.{u + 1})
        (aV : RV ⟶ SV) (aU : RU ⟶ SU)
        (cR : (proEtaleSheafInverseImage q CommRingCat.{u + 1}).obj RV ≅ RU)
        (cS : (proEtaleSheafInverseImage q CommRingCat.{u + 1}).obj SV ≅ SU)
        (comm : cR.hom ≫ aU = (proEtaleSheafInverseImage q CommRingCat.{u + 1}).map aV ≫ cS.hom)
        (N : proEtaleRingModules U SU) (W : V.ProEtᵒᵖ)
        (n : N.val.obj ((proEtaleBaseChange q).op.obj W)) :
        ((proEtaleRingRestrictionDirectImage q RV SV RU SU aV aU cR cS comm).hom.app N).val.app
          W n = n :=
      (Classical.choose_spec (proEtaleRingRestrictionDirectImage_existsUnique
        q RV SV RU SU aV aU cR cS comm)).1 N W n
    erw [dirApply g RZ SZ RY SY aZ aY cRg cSg commg
      ((proEtaleRingModuleDirectImage f SY SX cSf).obj N) W n]
    change ((conjugateEquiv ((proEtaleRingModuleAdjunction g RZ RY cRg).comp
        (proEtaleRingModuleAdjunction f RY RX cRf))
        (proEtaleRingModuleAdjunction (f ≫ g) RZ RX cRfg) κR.hom).app
          ((proEtaleRingRestrictScalars aX).obj N)).val.app W
        (((proEtaleRingRestrictionDirectImage f RY SY RX SX aY aX cRf cSf commf).hom.app
          N).val.app ((proEtaleBaseChange g).op.obj W) n) =
      ((proEtaleRingRestrictionDirectImage (f ≫ g) RZ SZ RX SX aZ aX cRfg cSfg
        commfg).hom.app N).val.app W
        (((conjugateEquiv ((proEtaleRingModuleAdjunction g SZ SY cSg).comp
          (proEtaleRingModuleAdjunction f SY SX cSf))
          (proEtaleRingModuleAdjunction (f ≫ g) SZ SX cSfg) κS.hom).app N).val.app W n)
    erw [dirApply f RY SY RX SX aY aX cRf cSf commf N ((proEtaleBaseChange g).op.obj W) n,
      dirApply (f ≫ g) RZ SZ RX SX aZ aX cRfg cSfg commfg N W _]
    obtain ⟨W⟩ := W
    erw [hκR ((proEtaleRingRestrictScalars aX).obj N) W n, hκS N W n]
    rfl
  have hm := congrArg (fun z ↦ z.app M) hc
  simpa only [q, TwoSquare.whiskerRight, TwoSquare.whiskerLeft, TwoSquare.vComp,
    TwoSquare.mk, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
    Category.comp_id, Category.assoc] using hm
end RestrictionComposition

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme

section ReductionComposition

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)

/-- The tower compositor induced by an ordinary module compositor. -/
abbrev towerCompositor {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (κ : stratumModulePull d (f ≫ g) ≅ stratumModulePull d g ⋙ stratumModulePull d f) :
    d.towerModulePull (f ≫ g) ≅ d.towerModulePull g ⋙ d.towerModulePull f :=
  (Functor.whiskeringRight ℕᵒᵖ _ _).mapIso κ ≪≫
    (Functor.whiskeringRightObjCompIso _ _).symm

/-- The completed derived pullback compositor is the localization of an ordinary module
compositor whose conjugate is the fibre-product pasting map on sections.
Source: Stacks Tag 0D6D (blueprint: proposition-composition-base-change-rf-shriek--4). -/
theorem AdicCoefficientDatum.pullComp_eq_triangle {X Y Z : Scheme.{u}} (f : X ⟶ Y)
    (g : Y ⟶ Z) :
    ∃ κ : stratumModulePull d (f ≫ g) ≅ stratumModulePull d g ⋙ stratumModulePull d f,
      d.pullComp f g = Functor.mapDerivedCategoryTriangleIso' κ ∧
      ∀ (N : proEtaleRingModules X (d.completedRing X)) (U : Z.ProEt)
        (m : ((proEtaleRingModuleDirectImage f (d.completedRing Y) (d.completedRing X)
            (d.integralRingIso f) ⋙ proEtaleRingModuleDirectImage g (d.completedRing Z)
              (d.completedRing Y) (d.integralRingIso g)).obj N).val.obj (Opposite.op U)),
        ((conjugateEquiv ((proEtaleRingModuleAdjunction g (d.completedRing Z)
              (d.completedRing Y) (d.integralRingIso g)).comp
            (proEtaleRingModuleAdjunction f (d.completedRing Y) (d.completedRing X)
              (d.integralRingIso f)))
            (proEtaleRingModuleAdjunction (f ≫ g) (d.completedRing Z) (d.completedRing X)
              (d.integralRingIso (f ≫ g))) κ.hom).app N).val.app (Opposite.op U) m =
          N.val.map ((MorphismProperty.Over.pullbackComp f g).hom.app U).op m := by
  obtain ⟨_, _, _, _, _, _, dS, hdS, _⟩ := proEtaleRingDerivedPullbackComposition f g
    (d.completedRing Z) (d.completedRing Y) (d.completedRing X) (d.integralRingIso g)
    (d.integralRingIso f) (d.integralRingIso (f ≫ g)) (d.integralRingIso_comp f g)
  refine ⟨(Adjunction.leftAdjointCompIso
    (proEtaleRingModuleAdjunction g (d.completedRing Z) (d.completedRing Y)
      (d.integralRingIso g))
    (proEtaleRingModuleAdjunction f (d.completedRing Y) (d.completedRing X)
      (d.integralRingIso f))
    (proEtaleRingModuleAdjunction (f ≫ g) (d.completedRing Z) (d.completedRing X)
      (d.integralRingIso (f ≫ g))) dS).symm, ?_, ?_⟩
  · exact proEtaleCanonicalDerivedPullback_normalization f g (d.completedRing Z)
      (d.completedRing Y) (d.completedRing X) (d.integralRingIso g) (d.integralRingIso f)
      (d.integralRingIso (f ≫ g)) (d.integralRingIso_comp f g).symm dS hdS
  · intro N U m
    rw [Iso.symm_hom, Adjunction.conjugateEquiv_leftAdjointCompIso_inv]
    exact hdS N U m

/-- Restriction to constant coefficients respects the inverse-image compositors on modules.
Source: Stacks, Modules on Sites, Tags 03D8 and 03D7 (blueprint:
proposition-composition-base-change-rf-shriek--4).
-/
theorem exchangeOrdinaryResPull_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (κ : stratumModulePull d (f ≫ g) ≅ stratumModulePull d g ⋙ stratumModulePull d f)
    (hκ : ∀ (N : proEtaleRingModules X (d.completedRing X)) (U : Z.ProEt)
        (m : ((proEtaleRingModuleDirectImage f (d.completedRing Y) (d.completedRing X)
            (d.integralRingIso f) ⋙ proEtaleRingModuleDirectImage g (d.completedRing Z)
              (d.completedRing Y) (d.integralRingIso g)).obj N).val.obj (Opposite.op U)),
        ((conjugateEquiv ((proEtaleRingModuleAdjunction g (d.completedRing Z)
              (d.completedRing Y) (d.integralRingIso g)).comp
            (proEtaleRingModuleAdjunction f (d.completedRing Y) (d.completedRing X)
              (d.integralRingIso f)))
            (proEtaleRingModuleAdjunction (f ≫ g) (d.completedRing Z) (d.completedRing X)
              (d.integralRingIso (f ≫ g))) κ.hom).app N).val.app (Opposite.op U) m =
          N.val.map ((MorphismProperty.Over.pullbackComp f g).hom.app U).op m)
    (M : proEtaleRingModules Z (d.completedRing Z)) :
    (proEtaleRingRestrictScalars (exchangeScalar d X)).map (κ.hom.app M) ≫
        (exchangeOrdinaryResPull d f).hom.app ((stratumModulePull d g).obj M) ≫
        (ProEtale.StrictTower.modulePullback A f).map ((exchangeOrdinaryResPull d g).hom.app M) =
      (exchangeOrdinaryResPull d (f ≫ g)).hom.app M ≫
        (ProEtale.StrictTower.moduleGComp A f g).hom.app
          ((proEtaleRingRestrictScalars (exchangeScalar d Z)).obj M) := by
  have hR : ∀ (N : ProEtale.StrictTower.Modules A X) (U : Z.ProEt)
      (m : ((ProEtale.StrictTower.moduleDirectImage A f ⋙
        ProEtale.StrictTower.moduleDirectImage A g).obj N).val.obj (Opposite.op U)),
      ((conjugateEquiv ((proEtaleRingModuleAdjunction g (ProEtale.StrictTower.coefficients A Z)
            (ProEtale.StrictTower.coefficients A Y) (ProEtale.StrictTower.constantRingIso A g)).comp
          (proEtaleRingModuleAdjunction f (ProEtale.StrictTower.coefficients A Y)
            (ProEtale.StrictTower.coefficients A X) (ProEtale.StrictTower.constantRingIso A f)))
          (proEtaleRingModuleAdjunction (f ≫ g) (ProEtale.StrictTower.coefficients A Z)
            (ProEtale.StrictTower.coefficients A X)
            (ProEtale.StrictTower.constantRingIso A (f ≫ g)))
          (ProEtale.StrictTower.moduleGComp A f g).hom).app N).val.app (Opposite.op U) m =
        N.val.map ((MorphismProperty.Over.pullbackComp f g).hom.app U).op m := by
    intro N U m
    rw [ProEtale.StrictTower.moduleGComp, Iso.symm_hom,
      Adjunction.conjugateEquiv_leftAdjointCompIso_inv]
    exact (Classical.choose_spec (ProEtale.StrictTower.moduleRComp_existsUnique A f g)).1 N U m
  have h := restrictionPullbackInv_comp f g
    (exchangeConstantRing Z A) (d.completedRing Z) (exchangeConstantRing Y A) (d.completedRing Y)
    (exchangeConstantRing X A) (d.completedRing X)
    (exchangeScalar d Z) (exchangeScalar d Y) (exchangeScalar d X)
    (exchangeConstantIso g A) (d.integralRingIso g) (exchangeConstantIso f A)
    (d.integralRingIso f) (exchangeConstantIso (f ≫ g) A) (d.integralRingIso (f ≫ g))
    (exchangeScalar_comm d g) (exchangeScalar_comm d f) (exchangeScalar_comm d (f ≫ g))
    (ProEtale.StrictTower.moduleGComp A f g) κ hR hκ M
  rw [← cancel_epi ((exchangeOrdinaryResPull d (f ≫ g)).inv.app M), Iso.inv_hom_id_app_assoc]
  have h' : (exchangeOrdinaryResPull d (f ≫ g)).inv.app M ≫
      (proEtaleRingRestrictScalars (exchangeScalar d X)).map (κ.hom.app M) =
      (ProEtale.StrictTower.moduleGComp A f g).hom.app
          ((proEtaleRingRestrictScalars (exchangeScalar d Z)).obj M) ≫
        (ProEtale.StrictTower.modulePullback A f).map
          ((exchangeOrdinaryResPull d g).inv.app M) ≫
        (exchangeOrdinaryResPull d f).inv.app ((stratumModulePull d g).obj M) := h.symm
  rw [reassoc_of% h', Iso.inv_hom_id_app_assoc, ← Functor.map_comp, Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits in
/-- Restriction to constant coefficients respects the derived inverse-image compositors.
Source: Stacks, Modules on Sites, Tags 03D8 and 03D7 (blueprint:
proposition-composition-base-change-rf-shriek--4).
-/
theorem exchangeResPull_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (κ : stratumModulePull d (f ≫ g) ≅ stratumModulePull d g ⋙ stratumModulePull d f)
    (hκ : ∀ (N : proEtaleRingModules X (d.completedRing X)) (U : Z.ProEt)
        (m : ((proEtaleRingModuleDirectImage f (d.completedRing Y) (d.completedRing X)
            (d.integralRingIso f) ⋙ proEtaleRingModuleDirectImage g (d.completedRing Z)
              (d.completedRing Y) (d.integralRingIso g)).obj N).val.obj (Opposite.op U)),
        ((conjugateEquiv ((proEtaleRingModuleAdjunction g (d.completedRing Z)
              (d.completedRing Y) (d.integralRingIso g)).comp
            (proEtaleRingModuleAdjunction f (d.completedRing Y) (d.completedRing X)
              (d.integralRingIso f)))
            (proEtaleRingModuleAdjunction (f ≫ g) (d.completedRing Z) (d.completedRing X)
              (d.integralRingIso (f ≫ g))) κ.hom).app N).val.app (Opposite.op U) m =
          N.val.map ((MorphismProperty.Over.pullbackComp f g).hom.app U).op m)
    (N : DerivedCategory (exchangeTowers Z (d.completedRing Z))) :
    (exchangeTowerRes d X).map
        ((Functor.mapDerivedCategoryTriangleIso' (towerCompositor d f g κ)).hom.app N) ≫
      (exchangeResPull d f).hom.app ((d.towerPull g).obj N) ≫
      (exchangeConstantPull (A := A) f).map ((exchangeResPull d g).hom.app N) =
    (exchangeResPull d (f ≫ g)).hom.app N ≫
      (ProEtale.StrictTower.gComp A f g).hom.app ((exchangeTowerRes d Z).obj N) := by
  have hq : ∀ M, (exchangeTowerModuleRes d X).map ((towerCompositor d f g κ).hom.app M) ≫
      (exchangeModuleResPull d f).hom.app ((d.towerModulePull g).obj M) ≫
      (exchangeTowerModulePull f (exchangeConstantRing Y A) (exchangeConstantRing X A)
        (exchangeConstantIso f A)).map ((exchangeModuleResPull d g).hom.app M) =
      (exchangeModuleResPull d (f ≫ g)).hom.app M ≫
        (ProEtale.StrictTower.towerGComp A f g).hom.app
          ((exchangeTowerModuleRes d Z).obj M) := by
    intro M
    apply NatTrans.ext
    funext n
    have h := exchangeOrdinaryResPull_comp d f g κ hκ (M.obj n)
    simp only [NatTrans.comp_app, towerCompositor, Iso.trans_hom, Functor.mapIso_hom,
      Iso.symm_hom, Functor.whiskeringRight_map_app_app, Functor.whiskeringRightObjCompIso,
      Iso.refl_inv, NatTrans.id_app, Functor.whiskeringRight_obj_map, Functor.whiskerRight_app,
      exchangeModuleResPull, NatIso.ofComponents_hom_app, Functor.isoWhiskerLeft_hom,
      Functor.whiskerLeft_app, ProEtale.StrictTower.towerGComp, Iso.refl_hom]
    erw [Category.comp_id, Category.comp_id]
    exact h
  have H := Functor.mapDerivedCategorySquareIso_comp (d.towerModulePull g)
    (d.towerModulePull f) (d.towerModulePull (f ≫ g))
    (ProEtale.StrictTower.towerPullback A g) (ProEtale.StrictTower.towerPullback A f)
    (ProEtale.StrictTower.towerPullback A (f ≫ g))
    (exchangeTowerModuleRes d Z) (exchangeTowerModuleRes d Y) (exchangeTowerModuleRes d X)
    (exchangeModuleResPull d g) (exchangeModuleResPull d f) (exchangeModuleResPull d (f ≫ g))
    (towerCompositor d f g κ) (ProEtale.StrictTower.towerGComp A f g) hq
  have H' := congrArg (fun e ↦ e.hom.app N) H
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Iso.symm_hom,
    Category.id_comp, Category.comp_id] at H'
  exact H'
end ReductionComposition

end AlgebraicGeometry.Scheme
