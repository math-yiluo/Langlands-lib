/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.DiscreteCoefficientModel
public import WeilConjectures.AlgebraicGeometry.FixedScalarComplexModel
public import WeilConjectures.AlgebraicGeometry.IntegralConstantModelRealization
import all WeilConjectures.AlgebraicGeometry.CompletedConstantAlgebraFlatQuotients
import all WeilConjectures.AlgebraicGeometry.ConstantCompletionCore
import WeilConjectures.AlgebraicGeometry.FixedScalarSmallCoordinates
import all WeilConjectures.AlgebraicGeometry.IntegralConstantCompletion
import WeilConjectures.AlgebraicGeometry.IntegralConstantSectionProjection
import all WeilConjectures.AlgebraicGeometry.IntegralModelsCompleteSectionPredicate
import all WeilConjectures.AlgebraicGeometry.IntegralModelsCompletionTransport
import WeilConjectures.CategoryTheory.InverseMateEquivalence

/-! # The normalized common first residue in constant-ring coordinates

Source: Stacks Tags 099L, 099M and 06YY, integral-models proof (1)--(2).
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option synthInstance.maxSize 2048
set_option linter.style.haveILetI false
universe u
open CategoryTheory CategoryTheory.Limits

open scoped CategoryTheory.Obj
attribute [local irreducible] AlgebraicGeometry.ProEtale.upperStarFromPoint
  Mod.extendScalars Mod.comap Functor.mapDerivedCategory Functor.leftDerivedFunctor
  Functor.pushforwardContinuousSheafificationCompatibility
  AlgebraicGeometry.Scheme.fixedScalarProEtaleSheafEquivalence
  AlgebraicGeometry.Scheme.sfbFixedScalarRestriction

namespace AlgebraicGeometry.ProEtale.IntegralModelsStacks

private local instance (priority := 100000) residueSmallAbSheafify (X : Scheme.{u}) :
    HasSheafify (Scheme.coefficientProEtaleModelTopology.{u, u} X) Ab.{u + 1} :=
  GrothendieckTopology.hasSheafify_of_isGrothendieckAbelian _ _

private local instance residueCommRingSheafify (X : Scheme.{u}) :
    HasSheafify (Scheme.ProEt.topology X) CommRingCat.{u + 1} :=
  WeilConjectures.integralCoefficientRingSheafify.{u, u} X

attribute [local irreducible] completedSectionIso integralSectionRingIso
  IntegralConstantModel.pointComparison
  WeilConjectures.purCoefficientIso Scheme.pbcCompletedComparison
  Scheme.CompletedConstantAlgebra.completionIso Scheme.CompletedConstantAlgebra.constantsIso

private local instance residueSiteSmall (X : Scheme.{u}) :
    EssentiallySmall.{u + 1} X.ProEt := essentiallySmallSelf.{0, u, u + 1} _

private local instance residueAbSheafify (X : Scheme.{u}) :
    HasSheafify (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1} :=
  WeilConjectures.integralCoefficientAbSheafify.{u, u} X

private local instance residueAbLocallyBijective (X : Scheme.{u}) :
    (Scheme.ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  WeilConjectures.integralCoefficientAbLocallyBijective.{u, u} X

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  WeilConjectures.integralCoefficientAbSheafify WeilConjectures.integralCoefficientRingSheafify
  WeilConjectures.integralCoefficientAbLocallyBijective
  WeilConjectures.integralReductionSiteEssentiallySmall WeilConjectures.integralOperationsSiteSmall
in
private def residueExtensionIso
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L : A ⥤ B} {U : B ⥤ A} {L' : C ⥤ D} {U' : D ⥤ C}
    {F : A ⥤ C} {G : B ⥤ D} [F.IsEquivalence] [G.IsEquivalence]
    (a : L ⊣ U) (b : L' ⊣ U') (e : U ⋙ F ≅ G ⋙ U') :
    L ⋙ G ≅ F ⋙ L' := by
  let α := ((mateEquiv a b).symm (TwoSquare.mk _ _ _ _ e.hom))
  letI : IsIso α := CategoryTheory.isIso_inverseMate_of_equivalences a b e
  exact (asIso α).symm

private def residueDerivedComposite
    {A B C : Type*} [Category A] [Category B] [Category C]
    [Abelian A] [Abelian B] [Abelian C]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
    (F : A ⥤ B) (G : B ⥤ C) (H : A ⥤ C)
    [F.Additive] [G.Additive] [H.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (e : F ⋙ G ≅ H) : F.mapDerivedCategory ⋙ G.mapDerivedCategory ≅
      H.mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso F G) ≪≫ Functor.mapDerivedCategoryNatIso e

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  WeilConjectures.integralCoefficientAbSheafify WeilConjectures.integralCoefficientRingSheafify
  WeilConjectures.integralCoefficientAbLocallyBijective
  WeilConjectures.integralReductionSiteEssentiallySmall WeilConjectures.integralOperationsSiteSmall
in
private def residueDerivedSquare
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (U : B ⥤ A) (V : D ⥤ C) (F : A ⥤ C) (G : B ⥤ D)
    [U.Additive] [V.Additive] [F.Additive] [G.Additive]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (e : U ⋙ F ≅ G ⋙ V) :
    U.mapDerivedCategory ⋙ F.mapDerivedCategory ≅
      G.mapDerivedCategory ⋙ V.mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso U F) ≪≫
    Functor.mapDerivedCategoryNatIso e ≪≫ (Functor.mapDerivedCategoryCompIso G V).symm

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  WeilConjectures.integralCoefficientAbSheafify WeilConjectures.integralCoefficientRingSheafify
  WeilConjectures.integralCoefficientAbLocallyBijective
  WeilConjectures.integralReductionSiteEssentiallySmall WeilConjectures.integralOperationsSiteSmall
in
private theorem residueCompletedAdjunction (X : Scheme.{u})
    {R S : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}} (φ : R ⟶ S) :
    Nonempty (Scheme.completedAdicDerivedChange X φ ⊣ Scheme.pbcDerivedRestrict φ) :=
  ⟨Scheme.pbcDerivedScalarAdjunction φ⟩

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  WeilConjectures.integralCoefficientAbSheafify WeilConjectures.integralCoefficientRingSheafify
  WeilConjectures.integralCoefficientAbLocallyBijective
  WeilConjectures.integralReductionSiteEssentiallySmall WeilConjectures.integralOperationsSiteSmall
in
private def residueDiscreteIso (X : Scheme.{u}) (A : Type u) [CommRing A]
    (d : Scheme.adicLisseConstantRing X (ULift.{u + 1} A) ≅
      InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
        (Scheme.ProEt.topology X) (condensedRingObj (discreteObj A) X)) :
    ConstantCompletion.constant (Scheme.coefficientProEtaleModelTopology.{u, u} X)
        (ULift.{u + 1} A) ≅ smallRing X (condensedRingObj (discreteObj A) X) :=
  ((Scheme.CompletedConstantAlgebra.constantsIso X).app
      (CommRingCat.of (ULift.{u + 1} A))).symm ≪≫
    (Scheme.CompletedConstantAlgebra.pushRing X).mapIso d

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  WeilConjectures.integralCoefficientAbSheafify WeilConjectures.integralCoefficientRingSheafify
  WeilConjectures.integralCoefficientAbLocallyBijective
  WeilConjectures.integralReductionSiteEssentiallySmall WeilConjectures.integralOperationsSiteSmall
in
private theorem residueConstantsIso_unit (X : Scheme.{u})
    (A : Type (u + 1)) [CommRing A]
    (U : Scheme.coefficientProEtaleSiteModel.{u, u} X) (a : A) :
    ((Scheme.CompletedConstantAlgebra.constantsIso X).app (CommRingCat.of A)).inv.hom.app
        (Opposite.op U)
        ((toSheafify (Scheme.coefficientProEtaleModelTopology.{u, u} X)
          ((Functor.const _).obj (CommRingCat.of A))).app (Opposite.op U) a) =
      (toSheafify (Scheme.ProEt.topology X)
        ((Functor.const _).obj (CommRingCat.of A))).app
          (Opposite.op (AsSmall.down.obj U)) a := by
  let down : Scheme.coefficientProEtaleSiteModel.{u, u} X ⥤ X.ProEt := AsSmall.down
  have h := down.toSheafify_pullbackSheafificationCompatibility CommRingCat.{u + 1}
      (Scheme.coefficientProEtaleModelTopology.{u, u} X) (Scheme.ProEt.topology X)
      ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of A))
  unfold Scheme.CompletedConstantAlgebra.constantsIso
  have hh := ConcreteCategory.congr_hom (congr_app h (Opposite.op U)) a
  dsimp only [down, Scheme.CompletedConstantAlgebra.smallTopology,
    Scheme.coefficientProEtaleModelTopology, constantSheaf, NatIso.ofComponents,
    Iso.app, Iso.symm, Functor.comp_obj, Functor.whiskerLeft_app] at hh ⊢
  exact hh

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  WeilConjectures.integralCoefficientAbSheafify WeilConjectures.integralCoefficientRingSheafify
  WeilConjectures.integralCoefficientAbLocallyBijective
  WeilConjectures.integralReductionSiteEssentiallySmall WeilConjectures.integralOperationsSiteSmall
in
private theorem residueDiscreteIso_unit (X : Scheme.{u}) (A : Type u) [CommRing A]
    (d : Scheme.adicLisseConstantRing X (ULift.{u + 1} A) ≅
      InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
        (Scheme.ProEt.topology X) (condensedRingObj (discreteObj A) X))
    (hd : DiscreteSectionRingNormalized X A d)
    (U : Scheme.coefficientProEtaleSiteModel.{u, u} X) (a : ULift.{u + 1} A) :
    (residueDiscreteIso X A d).hom.hom.app (Opposite.op U)
        ((toSheafify (Scheme.coefficientProEtaleModelTopology.{u, u} X)
          ((Functor.const _).obj (CommRingCat.of (ULift.{u + 1} A)))).app
            (Opposite.op U) a) =
      (discreteCoefficientAbelianIso X A).hom.hom.app (Opposite.op (AsSmall.down.obj U))
        ((toSheafify (Scheme.ProEt.topology X)
          ((Functor.const _).obj (AddCommGrpCat.of (ULift.{u + 1} A)))).app
            (Opposite.op (AsSmall.down.obj U)) a) := by
  change d.hom.hom.app (Opposite.op (AsSmall.down.obj U))
    (((Scheme.CompletedConstantAlgebra.constantsIso X).app
      (CommRingCat.of (ULift.{u + 1} A))).inv.hom.app (Opposite.op U) _) = _
  rw [residueConstantsIso_unit]
  exact hd (Opposite.op (AsSmall.down.obj U)) a

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  WeilConjectures.integralCoefficientAbSheafify WeilConjectures.integralCoefficientRingSheafify
  WeilConjectures.integralCoefficientAbLocallyBijective
  WeilConjectures.integralReductionSiteEssentiallySmall WeilConjectures.integralOperationsSiteSmall
in
private theorem residueDiscreteIso_relabel (X : Scheme.{u}) (A : Type u) [CommRing A]
    (d : Scheme.adicLisseConstantRing X (ULift.{u + 1} A) ≅
      InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
        (Scheme.ProEt.topology X) (condensedRingObj (discreteObj A) X))
    (hd : DiscreteSectionRingNormalized X A d)
    (k : Type (u + 1)) [CommRing k] (e : ULift.{u + 1} A ≃+* k) :
    DiscreteCoefficientNormalized X A k e
      ((constantSheaf (Scheme.coefficientProEtaleModelTopology.{u, u} X)
        CommRingCat.{u + 1}).mapIso e.symm.toCommRingCatIso ≪≫ residueDiscreteIso X A d) := by
  intro U a
  let J := Scheme.coefficientProEtaleModelTopology.{u, u} X
  let η := toSheafify J ((Functor.const _).obj (CommRingCat.of k))
  let η' := toSheafify J ((Functor.const _).obj (CommRingCat.of (ULift.{u + 1} A)))
  have h := ConcreteCategory.congr_hom (congr_app
    (toSheafify_naturality J ((Functor.const _).map
      (CommRingCat.ofHom e.symm.toRingHom))) (Opposite.op U)) (e a)
  change η'.app (Opposite.op U) (e.symm (e a)) =
    ((constantSheaf J CommRingCat.{u + 1}).map e.symm.toCommRingCatIso.hom).hom.app
      (Opposite.op U) (η.app (Opposite.op U) (e a)) at h
  rw [e.symm_apply_apply] at h
  change (residueDiscreteIso X A d).hom.hom.app (Opposite.op U)
    (((constantSheaf J CommRingCat.{u + 1}).map e.symm.toCommRingCatIso.hom).hom.app
      (Opposite.op U) (η.app (Opposite.op U) (e a))) = _
  rw [← h]
  exact residueDiscreteIso_unit X A d hd U a

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  WeilConjectures.integralCoefficientAbSheafify WeilConjectures.integralCoefficientRingSheafify
  WeilConjectures.integralCoefficientAbLocallyBijective
  WeilConjectures.integralReductionSiteEssentiallySmall WeilConjectures.integralOperationsSiteSmall
in
private theorem residueDiscreteIso_natural (X : Scheme.{u})
    {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)
    (d : Scheme.adicLisseConstantRing X (ULift.{u + 1} A) ≅
      InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
        (Scheme.ProEt.topology X) (condensedRingObj (discreteObj A) X))
    (e : Scheme.adicLisseConstantRing X (ULift.{u + 1} B) ≅
      InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
        (Scheme.ProEt.topology X) (condensedRingObj (discreteObj B) X))
    (h : d.hom ≫ sectionMap X ((upperStarFromPoint X).map (discreteMap f)) =
      (constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).map
        (CommRingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
          (f.comp ULift.ringEquiv.toRingHom))) ≫ e.hom) :
    (residueDiscreteIso X A d).hom ≫
        smallMap X ((upperStarFromPoint X).map (discreteMap f)) =
      (constantSheaf (Scheme.coefficientProEtaleModelTopology.{u, u} X)
        CommRingCat.{u + 1}).map
          (CommRingCat.ofHom
            ((ULift.ringEquiv : ULift.{u + 1} B ≃+* B).symm.toRingHom.comp
              (f.comp (ULift.ringEquiv : ULift.{u + 1} A ≃+* A).toRingHom))) ≫
        (residueDiscreteIso X B e).hom := by
  let F := Scheme.CompletedConstantAlgebra.pushRing X
  let g : CommRingCat.of (ULift.{u + 1} A) ⟶
      CommRingCat.of (ULift.{u + 1} B) :=
    CommRingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
      (f.comp ULift.ringEquiv.toRingHom))
  have h' := (Scheme.CompletedConstantAlgebra.constantsIso X).inv.naturality g
  dsimp only [residueDiscreteIso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
  change _ ≫ F.map d.hom ≫
    F.map (sectionMap X ((upperStarFromPoint X).map (discreteMap f))) = _
  rw [← F.map_comp, h, F.map_comp]
  have hh := congrArg
    (fun f ↦ f ≫ F.map e.hom) h'.symm
  dsimp only [F, g, ConstantCompletion.constant, Iso.app,
    Scheme.CompletedConstantAlgebra.smallTopology,
    Scheme.coefficientProEtaleModelTopology, Functor.comp_map] at hh ⊢
  simpa only [Category.assoc] using hh

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  WeilConjectures.integralCoefficientAbSheafify WeilConjectures.integralCoefficientRingSheafify
  WeilConjectures.integralCoefficientAbLocallyBijective
  WeilConjectures.integralReductionSiteEssentiallySmall WeilConjectures.integralOperationsSiteSmall
in
private def residueSiteScalarSquare (X : Scheme.{u})
    {R S : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}} (φ : R ⟶ S) :
    Scheme.pbcRestrict φ ⋙ Scheme.proEtaleModuleToModel ((Scheme.adicLisseForget X).obj R) ≅
      Scheme.proEtaleModuleToModel ((Scheme.adicLisseForget X).obj S) ⋙
        ConstantCompletion.res ((Scheme.sfbModelRings X).map φ) := Iso.refl _

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  WeilConjectures.integralCoefficientAbSheafify WeilConjectures.integralCoefficientRingSheafify
  WeilConjectures.integralCoefficientAbLocallyBijective
  WeilConjectures.integralReductionSiteEssentiallySmall WeilConjectures.integralOperationsSiteSmall
in
private def residueScalarSquare
    {C : Type (u + 1)} [SmallCategory C] {J : GrothendieckTopology C}
    {R S R' S' : Sheaf J CommRingCat.{u + 1}}
    (q : R ⟶ S) (q' : R' ⟶ S') (a : R' ≅ R) (b : S' ≅ S)
    (h : a.hom ≫ q = q' ≫ b.hom) :
    ConstantCompletion.res q ⋙ ConstantCompletion.res a.hom ≅
      ConstantCompletion.res b.hom ⋙ ConstantCompletion.res q' :=
  ConstantCompletion.resCompIso a.hom q (q' ≫ b.hom) h ≪≫
    (ConstantCompletion.resCompIso q' b.hom (q' ≫ b.hom) rfl).symm

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  WeilConjectures.integralCoefficientAbSheafify WeilConjectures.integralCoefficientRingSheafify
  WeilConjectures.integralCoefficientAbLocallyBijective
  WeilConjectures.integralReductionSiteEssentiallySmall WeilConjectures.integralOperationsSiteSmall
in
private def residueSmallScalarSquare (X : Scheme.{u})
    {R S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
    (f : R ⟶ S) [IsMonHom f]
    {R' S' : Sheaf (Scheme.coefficientProEtaleModelTopology.{u, u} X) CommRingCat.{u + 1}}
    (q : R' ⟶ S') (a : R' ≅ smallRing X R) (b : S' ≅ smallRing X S)
    (h : a.hom ≫ smallMap X f = q ≫ b.hom) :
    Mod.comap f ⋙ (smallModules X R ⋙ ConstantCompletion.res a.hom) ≅
      (smallModules X S ⋙ ConstantCompletion.res b.hom) ⋙ ConstantCompletion.res q :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (smallRestrictionIso X f) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (residueScalarSquare (smallMap X f) q a b h) ≪≫
    (Functor.associator _ _ _).symm

private def residueRestrictCancelIso
    {C : Type (u + 1)} [SmallCategory C] (J : GrothendieckTopology C)
    {R S : Sheaf J RingCat.{u + 1}}
    (α : R ⟶ S) (β : S ⟶ R) (h : α ≫ β = 𝟙 R) :
    SheafOfModules.restrictScalars β ⋙ SheafOfModules.restrictScalars α ≅
      𝟭 (SheafOfModules.{u + 1} R) := by
  have hU (U : Cᵒᵖ) : (β.hom.app U).hom.comp (α.hom.app U).hom =
      RingHom.id (R.obj.obj U) :=
    congrArg RingCat.Hom.hom (congr_app (congrArg (fun k : R ⟶ R ↦ k.hom) h) U)
  refine NatIso.ofComponents (fun M ↦ (SheafOfModules.fullyFaithfulForget R).preimageIso
    (PresheafOfModules.isoMk (fun U ↦
      (ModuleCat.restrictScalarsComp'App (α.hom.app U).hom (β.hom.app U).hom
        (RingHom.id (R.obj.obj U)) (hU U).symm (M.val.obj U)).symm ≪≫
      (ModuleCat.restrictScalarsId (R.obj.obj U)).app (M.val.obj U)) ?_)) ?_
  · intro U V f
    ext x
    rfl
  · intro M N f
    ext U x
    rfl

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  WeilConjectures.integralCoefficientAbSheafify WeilConjectures.integralCoefficientRingSheafify
  WeilConjectures.integralCoefficientAbLocallyBijective
  WeilConjectures.integralReductionSiteEssentiallySmall WeilConjectures.integralOperationsSiteSmall
in
private theorem residueRestrictionEquivalence
    {C : Type (u + 1)} [SmallCategory C] {J : GrothendieckTopology C}
    {R S : Sheaf J CommRingCat.{u + 1}} (e : R ≅ S) :
    (ConstantCompletion.res e.hom).IsEquivalence := by
  let c := (sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso e
  let transport := CategoryTheory.Equivalence.mk (SheafOfModules.restrictScalars c.hom)
    (SheafOfModules.restrictScalars c.inv)
    (residueRestrictCancelIso J c.inv c.hom c.inv_hom_id).symm
    (residueRestrictCancelIso J c.hom c.inv c.hom_inv_id)
  exact transport.isEquivalence_functor

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  WeilConjectures.integralCoefficientAbLocallyBijective
  WeilConjectures.integralCoefficientAbSheafify WeilConjectures.integralCoefficientRingSheafify
  WeilConjectures.integralReductionSiteEssentiallySmall
  WeilConjectures.integralOperationsSiteSmall in
/-- Tensoring internal modules preserves the small colimits used in totalization.
Source: closedness of internal modules, Stacks Tag 03EK
(auxiliary; not a blueprint node).
Proof: closedness makes left tensor a left adjoint; symmetry identifies right tensor with it.
-/
theorem residueTensorColimits (X : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R] :
    (∀ M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R,
      PreservesColimitsOfSize.{0, 0} (MonoidalCategory.tensorLeft M)) ∧
    (∀ M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R,
      PreservesColimitsOfSize.{0, 0} (MonoidalCategory.tensorRight M)) := by
  let C := Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R
  let : MonoidalClosed C := by
    refine @Mod.monoidalClosed.{u + 1, u + 2}
      (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) _ _ _ _ _ _ R ‹MonObj R› ?_
  let : SymmetricCategory C := by
    refine @Mod.symmetricCategory.{u + 1, u + 2}
      (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) _ _ _ _ _ _ R ‹MonObj R› ?_
  constructor
  · intro M
    exact (ihom.adjunction M).leftAdjoint_preservesColimits
  · intro M
    let : PreservesColimitsOfSize.{0, 0} (MonoidalCategory.tensorLeft M) :=
      (ihom.adjunction M).leftAdjoint_preservesColimits
    exact preservesColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight M)

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  WeilConjectures.integralCoefficientAbLocallyBijective
  WeilConjectures.integralCoefficientAbSheafify WeilConjectures.integralCoefficientRingSheafify
  WeilConjectures.integralReductionSiteEssentiallySmall
  WeilConjectures.integralOperationsSiteSmall in
/-- Internal modules admit functorial flat resolutions with the specified scalar structure.
Source: the free-module flat resolution, Stacks Tag 06YS
(auxiliary; not a blueprint node).
Proof: apply the existing internal-module construction to flat resolutions of abelian sheaves.
-/
theorem residueFlatResolution (X : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R] :
    Abelian.HasFunctorialFlatResolution (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R) := by
  refine @Mod.hasFunctorialFlatResolution.{u + 1, u + 2}
    (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) _ _ _ _ _ _ R ‹MonObj R› ?_ _

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  WeilConjectures.integralCoefficientAbLocallyBijective
  WeilConjectures.integralCoefficientAbSheafify WeilConjectures.integralCoefficientRingSheafify
  WeilConjectures.integralReductionSiteEssentiallySmall
  WeilConjectures.integralOperationsSiteSmall in
/-- Scalar extension preserves quasi-isomorphisms between K-flat internal complexes.
Source: derived scalar extension, Stacks Tag 06YY
(auxiliary; not a blueprint node).
Proof: apply the existing internal-module scalar-extension theorem with these scalar objects.
-/
theorem residueExtensionKFlat (X : Scheme.{u})
    (R S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
    (f : R ⟶ S) [IsMonHom f] :
    letI := (residueTensorColimits X R).1
    letI := (residueTensorColimits X R).2
    letI := residueFlatResolution X R
    (Mod.extendScalars f).PreservesKFlatQuasiIso := by
  refine @Mod.preservesKFlatQuasiIso.{u + 1, u + 2}
    (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) _ _ _ _ _ _ _ _
    R S ‹MonObj R› ‹MonObj S› ?_ ?_ f _
  have hb : (AlgebraicGeometry.ProEtale.sheafSymmetricCategory
      (A := Ab.{u + 1}) X).toBraidedCategory =
      AlgebraicGeometry.ProEtale.sheafBraidedCategory Ab.{u + 1} X := by rfl
  rw [hb]
  exact ‹IsCommMonObj S›

/-- The normalized quotient equivalence, oriented from the lifted original residue ring.
Source: the existing integralCoefficientULift, normalized on quotient representatives
(auxiliary; not a blueprint node). -/
def integralResidueScalarEquiv (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] :
    ULift.{u + 1} (Padic.coefficientExtensionRing l E 1) ≃+*
      (IntegralConstantCompletion.integers l E ⧸
        IntegralConstantCompletion.ideal l E ^ (0 + 1)) :=
  (Scheme.integralCoefficientULift l E 0).symm

attribute [local irreducible] scalarMap residueMap IntegralConstantModel.modulesFunctor
  discreteCoefficientModel smallModules HasDerivedCategory.standard
  ConstantCompletion.derivedExtension ConstantCompletion.extend
  Scheme.completedAdicChangeData Scheme.completedAdicDerivedChange
  Functor.rightDerivedFunctor
  residueExtensionIso residueDerivedComposite residueDerivedSquare residueDiscreteIso
  residueSiteScalarSquare residueScalarSquare residueSmallScalarSquare

-- The exact restriction squares instantiate several derived scalar adjunctions.
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  WeilConjectures.integralCoefficientAbLocallyBijective
  WeilConjectures.integralCoefficientAbSheafify WeilConjectures.integralCoefficientRingSheafify
  WeilConjectures.integralReductionSiteEssentiallySmall
  WeilConjectures.integralOperationsSiteSmall in
/-- The two derived first residues are isomorphic after the normalized discrete scalar
model. No constructibility, Tor condition, completeness, or etale-origin hypothesis occurs.

Source: Stacks Tags 099L, 099M and 06YY; integral-models proof (1)--(2).
(auxiliary; not a blueprint node).

Proof: the quotient ring equivalence integralResidueScalarEquiv sends the lifted class
of x to the class of its lift. Its representative formula makes the first quotient square
commute. The normalized discrete coefficient map identifies the internal scalar quotient
with the constant quotient ring on the small site: both maps agree on every constant
section, and sheafification detects equality there. The integral realization is the
section-action functor followed by the two coefficient restrictions whose isomorphisms
commute with every finite projection. Apply integral_constant_completion at index zero.
On a flat-term K-flat representative of K its normalized common-quotient comparison
is the identity on balanced pure tensors. Internal-section tensor comparison and site
precomposition carry this to the displayed discreteCoefficientModel. On the other side,
constant scalar restriction followed by its inverse and site precomposition identify the
localized complex with fixedScalarDerivedModel of the literal sfbResidueComplex.
The localization comparison is used for the chosen Q.objPreimage in sfbResidueComplex;
its Q.objObjPreimageIso removes this choice. All factors preserve quasi-isomorphisms,
so the representative comparison descends to the displayed isomorphism. Completeness is
not used: the finite common quotient comparison applies to every input K. The equations
also hold for the zero residue and on the empty scheme.
-/
theorem integral_residue_model_comparison (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u})
    (c : ConstantCompletion.constant (Scheme.coefficientProEtaleModelTopology.{u, u} X)
        (IntegralConstantCompletion.integers l E ⧸
          IntegralConstantCompletion.ideal l E ^ (0 + 1)) ≅
      smallRing X (condensedRingObj
        (discreteObj (Padic.coefficientExtensionRing l E 1)) X))
    (hc : DiscreteCoefficientNormalized X (Padic.coefficientExtensionRing l E 1) _
      (integralResidueScalarEquiv l E) c)
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (integersObj l E) X))) :
    letI := (residueTensorColimits X
      (condensedRingObj (discreteObj (Padic.coefficientExtensionIntegers l E)) X)).1
    letI := (residueTensorColimits X
      (condensedRingObj (discreteObj (Padic.coefficientExtensionIntegers l E)) X)).2
    letI := residueFlatResolution X
      (condensedRingObj (discreteObj (Padic.coefficientExtensionIntegers l E)) X)
    letI := residueExtensionKFlat X _ _ (residueMap l E X)
    letI := HasDerivedCategory.standard (ConstantCompletion.Mod
      (ConstantCompletion.constant (Scheme.coefficientProEtaleModelTopology.{u, u} X)
        (IntegralConstantCompletion.integers l E ⧸
          IntegralConstantCompletion.ideal l E ^ (0 + 1))))
    Nonempty
      ((discreteCoefficientModel X
          (Padic.coefficientExtensionRing l E 1) _ c).mapDerivedCategory.obj
        (show DerivedCategory.{u + 1}
          (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
            (condensedRingObj (discreteObj (Padic.coefficientExtensionRing l E 1)) X)) from
          (Mod.extendScalars (residueMap l E X)).leftDerivedFunctor.obj
            ((restriction l E X).obj K)) ≅
      Scheme.fixedScalarDerivedModel X
        (IntegralConstantCompletion.integers l E ⧸
          IntegralConstantCompletion.ideal l E ^ (0 + 1))
        (Scheme.sfbResidueComplex X (IntegralConstantCompletion.ideal l E)
          ((IntegralConstantModel.derived l E X).functor.obj K))) := by
  classical
  let A := IntegralConstantCompletion.integers l E
  let I := IntegralConstantCompletion.ideal l E
  let J := Scheme.coefficientProEtaleModelTopology.{u, u} X
  let k := A ⧸ I ^ (0 + 1)
  let R := condensedRingObj (discreteObj (Padic.coefficientExtensionIntegers l E)) X
  let B := condensedRingObj (integersObj l E) X
  let S := condensedRingObj (discreteObj (Padic.coefficientExtensionRing l E 1)) X
  letI := (residueTensorColimits X R).1
  letI := (residueTensorColimits X R).2
  letI := residueFlatResolution X R
  letI := residueExtensionKFlat X _ _ (residueMap l E X)
  letI := HasDerivedCategory.standard (ConstantCompletion.Mod (ConstantCompletion.constant J k))
  letI := HasDerivedCategory.standard (ConstantCompletion.Mod (ConstantCompletion.constant J A))
  letI := HasDerivedCategory.standard (ConstantCompletion.Mod
    (ConstantCompletion.completed J A I))
  letI : HasDerivedCategory (ConstantCompletion.Mod
      (ConstantCompletion.coefficients J A I false)) := HasDerivedCategory.standard _
  letI : HasDerivedCategory (ConstantCompletion.Mod
      (ConstantCompletion.coefficients J A I true)) := HasDerivedCategory.standard _
  let F := Scheme.CompletedConstantAlgebra.pushRing X
  let comparisons := (integral_constant_section_projection l E X).exists.choose
  let i := comparisons.integers
  let j := comparisons.residue
  let a := residueDiscreteIso X (Padic.coefficientExtensionIntegers l E) i
  let b₀ := Scheme.CompletedConstantAlgebra.completionIso X I
  let b := F.mapIso (completedSectionIso l E X).symm ≪≫ b₀
  let t := (Scheme.CompletedConstantAlgebra.constantsIso X).app (CommRingCat.of k)
  let q := IntegralConstantCompletion.quotientMap l E X false 0
  let p := IntegralConstantCompletion.quotientMap l E X true 0
  let φ := IntegralConstantCompletion.scalarMap l E X
  let π : Scheme.adicLisseCompletedRing X I ⟶ Scheme.adicLisseConstantRing X k :=
    limit.π (Scheme.adicLisseRingSystem X I) (Opposite.op 0)
  have hφ : a.hom ≫ smallMap X (scalarMap l E X) = φ ≫ b.inv := by
    have h := Scheme.CompletedConstantAlgebra.coefficientMap_eq X I
      (i.hom ≫ sectionMap X (scalarMap l E X) ≫ (completedSectionIso l E X).inv)
      comparisons.projection
    apply (cancel_mono b.hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    calc
      a.hom ≫ smallMap X (scalarMap l E X) ≫ b.hom =
          ((Scheme.CompletedConstantAlgebra.constantsIso X).app
            (CommRingCat.of A)).inv ≫
          (F.map (i.hom ≫ sectionMap X (scalarMap l E X) ≫
            (completedSectionIso l E X).inv) ≫ b₀.hom) := by
        simp only [a, residueDiscreteIso, b, Iso.trans_hom, Functor.mapIso_hom,
          Iso.symm_hom, F.map_comp, Category.assoc]
        rfl
      _ = φ := by
        rw [h]
        exact Iso.inv_hom_id_assoc
          ((Scheme.CompletedConstantAlgebra.constantsIso X).app (CommRingCat.of A)) φ
  have hq : a.hom ≫ smallMap X (residueMap l E X) = q ≫ c.hom := by
    let e := integralResidueScalarEquiv l E
    let g := CommRingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
      ((Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E 1)).comp
        ULift.ringEquiv.toRingHom))
    have hg : CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (0 + 1))) ≫
        e.symm.toCommRingCatIso.hom = g := by
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro r
      exact (Scheme.integralCoefficientULift_exists l E 0).exists.choose_spec r
    have hc' := discreteCoefficientNormalized_unique X
      (Padic.coefficientExtensionRing l E 1) k e hc
      (residueDiscreteIso_relabel X (Padic.coefficientExtensionRing l E 1) j
        comparisons.residue_normalized k e)
    rw [hc']
    unfold residueMap
    change a.hom ≫ smallMap X ((upperStarFromPoint X).map (discreteMap
      (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E 1)))) = _
    rw [residueDiscreteIso_natural X _ i j comparisons.reduction_naturality]
    change (constantSheaf J CommRingCat.{u + 1}).map g ≫ _ =
      (constantSheaf J CommRingCat.{u + 1}).map
        (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (0 + 1)))) ≫
          (constantSheaf J CommRingCat.{u + 1}).map e.symm.toCommRingCatIso.hom ≫ _
    rw [← Category.assoc, ← Functor.map_comp, hg]
  have hp : b₀.inv ≫ F.map π = p ≫ t.inv := by
    apply (Iso.eq_comp_inv t).mpr
    rw [Category.assoc]
    have h := Scheme.CompletedConstantAlgebra.completionIso_projection X I 0
    change b₀.hom ≫ p = F.map π ≫ t.hom at h
    rw [← h, Iso.inv_hom_id_assoc]
  let E₀ := discreteCoefficientModel X (Padic.coefficientExtensionIntegers l E) A a
  let E₁ := discreteCoefficientModel X (Padic.coefficientExtensionRing l E 1) k c
  let EB := smallModules X B ⋙ ConstantCompletion.res b.inv
  let TB : Scheme.proEtaleRingModules X (Scheme.adicLisseCompletedRing X I) ⥤
      ConstantCompletion.Mod (F.obj (Scheme.adicLisseCompletedRing X I)) :=
    Scheme.proEtaleModuleToModel ((Scheme.adicLisseForget X).obj
      (Scheme.adicLisseCompletedRing X I))
  let TS : Scheme.proEtaleRingModules X (Scheme.adicLisseConstantRing X k) ⥤
      ConstantCompletion.Mod (F.obj (Scheme.adicLisseConstantRing X k)) :=
    Scheme.proEtaleModuleToModel ((Scheme.adicLisseForget X).obj
      (Scheme.adicLisseConstantRing X k))
  let FC : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) B ⥤
      Scheme.proEtaleRingModules X (Scheme.adicLisseCompletedRing X I) :=
    IntegralConstantModel.modulesFunctor l E X
  letI : FC.Additive := IntegralConstantModel.modulesFunctor_additive l E X
  letI : FC.IsEquivalence := IntegralConstantModel.modulesFunctor_isEquivalence l E X
  let HB := TB ⋙ ConstantCompletion.res b₀.inv
  let HS := Scheme.sfbFixedScalarRestriction X k ⋙
    (Scheme.fixedScalarProEtaleSheafEquivalence X k).functor
  letI : E₀.IsEquivalence := discreteCoefficientModel_isEquivalence X _ _ a
  letI : E₁.IsEquivalence := discreteCoefficientModel_isEquivalence X _ _ c
  letI : E₀.Additive := discreteCoefficientModel_additive X _ _ a
  letI : E₁.Additive := discreteCoefficientModel_additive X _ _ c
  letI : (smallModules X B).IsEquivalence := smallModules_equivalence X B
  letI : (smallModules X B).Additive := smallModules_additive X B
  letI : (ConstantCompletion.res b.inv).IsEquivalence := residueRestrictionEquivalence b.symm
  letI : EB.IsEquivalence := inferInstanceAs
    (smallModules X B ⋙ ConstantCompletion.res b.inv).IsEquivalence
  letI : EB.Additive := inferInstanceAs
    (smallModules X B ⋙ ConstantCompletion.res b.inv).Additive
  letI : TB.IsEquivalence := (toModelEquivalence X _).isEquivalence_functor
  letI : TS.IsEquivalence := (toModelEquivalence X _).isEquivalence_functor
  letI : TB.Additive := Functor.additive_of_preserves_binary_products TB
  letI : TS.Additive := Functor.additive_of_preserves_binary_products TS
  letI : (ConstantCompletion.res b₀.inv).IsEquivalence := residueRestrictionEquivalence b₀.symm
  letI : (ConstantCompletion.res t.inv).IsEquivalence := residueRestrictionEquivalence t.symm
  letI : HB.IsEquivalence := Functor.isEquivalence_trans TB (ConstantCompletion.res b₀.inv)
  letI : HB.Additive := Functor.additive_of_preserves_binary_products HB
  letI : (TS ⋙ ConstantCompletion.res t.inv).IsEquivalence :=
    Functor.isEquivalence_trans TS (ConstantCompletion.res t.inv)
  have ht : ∀ (U : Scheme.coefficientProEtaleSiteModel.{u, u} X) (r : k),
      t.hom.hom.app (Opposite.op U)
          ((toSheafify (Scheme.ProEt.topology X)
            ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of k))).app
              (Opposite.op (AsSmall.down.obj U)) r) =
        (toSheafify J ((Functor.const _).obj (CommRingCat.of k))).app (Opposite.op U) r := by
    intro U r
    rw [← residueConstantsIso_unit X k U r]
    exact ConcreteCategory.congr_hom
      (congrArg (fun f ↦ f.hom.app (Opposite.op U)) t.inv_hom_id) _
  obtain ⟨hS₀⟩ := Scheme.fixed_scalar_small_coordinates X k t ht
  have hS : HS ≅ TS ⋙ ConstantCompletion.res t.inv := hS₀
  letI : HS.IsEquivalence := Functor.isEquivalence_of_iso hS.symm
  letI : HS.Additive := inferInstanceAs
    (Scheme.sfbFixedScalarRestriction X k ⋙
      (Scheme.fixedScalarProEtaleSheafEquivalence X k).functor).Additive
  let e₀ : Mod.comap (residueMap l E X) ⋙ E₀ ≅ E₁ ⋙ ConstantCompletion.res q := by
    dsimp only [E₀, E₁]
    unfold discreteCoefficientModel
    exact residueSmallScalarSquare X (residueMap l E X) q a c hq
  let eφ : Mod.comap (scalarMap l E X) ⋙ E₀ ≅ EB ⋙ ConstantCompletion.res φ := by
    dsimp only [E₀, EB]
    unfold discreteCoefficientModel
    exact residueSmallScalarSquare X (scalarMap l E X) φ a b.symm hφ
  let eπ : Scheme.pbcRestrict π ⋙ HB ≅ HS ⋙ ConstantCompletion.res p :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (residueSiteScalarSquare X π) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft TS (residueScalarSquare (F.map π) p b₀.symm t.symm hp) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight hS.symm (ConstantCompletion.res p)
  have hqadj := (IntegralConstantCompletion.derived_scalar_adjunction q).some
  have hpadj := (IntegralConstantCompletion.derived_scalar_adjunction p).some
  let adj₀ := ((Mod.extendRestrictAdjunction (residueMap l E X)).derivedAdjunction).ofNatIsoRight
    (Mod.comap (residueMap l E X)).rightDerivedFunctorIsoMapDerivedCategory
  let d₀ : (Mod.extendScalars (residueMap l E X)).leftDerivedFunctor ⋙
      E₁.mapDerivedCategory ≅ E₀.mapDerivedCategory ⋙ ConstantCompletion.extend q :=
    residueExtensionIso adj₀ hqadj
      (residueDerivedSquare (Mod.comap (residueMap l E X)) (ConstantCompletion.res q) E₀ E₁ e₀)
  let dφ : (Mod.comap (scalarMap l E X)).mapDerivedCategory ⋙ E₀.mapDerivedCategory ≅
      EB.mapDerivedCategory ⋙ (ConstantCompletion.res φ).mapDerivedCategory :=
    residueDerivedSquare (Mod.comap (scalarMap l E X)) (ConstantCompletion.res φ) E₀ EB eφ
  let dπ : Scheme.completedAdicDerivedChange X π ⋙ HS.mapDerivedCategory ≅
      HB.mapDerivedCategory ⋙ ConstantCompletion.extend p :=
    residueExtensionIso (residueCompletedAdjunction X π).some hpadj
      (residueDerivedSquare (Scheme.pbcRestrict π) (ConstantCompletion.res p) HB HS eπ)
  let eB : FC ⋙ HB ≅ EB :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (smallModulesSectionIso l E X) (ConstantCompletion.res b₀.inv) ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (smallModules X B)
        (ConstantCompletion.resCompIso b₀.inv
          (F.map (completedSectionIso l E X).hom) b.inv rfl)
  let dB : FC.mapDerivedCategory ⋙ HB.mapDerivedCategory ≅ EB.mapDerivedCategory :=
    residueDerivedComposite FC HB EB eB
  let K' := (IntegralConstantModel.derived l E X).functor.obj K
  let P := DerivedCategory.Q.objPreimage ((Scheme.completedAdicDerivedChange X π).obj K')
  let df : Scheme.fixedScalarDerivedModel X k (Scheme.sfbResidueComplex X I K') ≅
      HS.mapDerivedCategory.obj ((Scheme.completedAdicDerivedChange X π).obj K') := by
    let H := Scheme.sfbFixedScalarRestriction X k
    let G := (Scheme.fixedScalarProEtaleSheafEquivalence X k).functor
    letI : G.IsEquivalence :=
      (Scheme.fixedScalarProEtaleSheafEquivalence X k).isEquivalence_functor
    letI : (H ⋙ G).IsEquivalence := inferInstanceAs HS.IsEquivalence
    letI : H.IsEquivalence := Functor.isEquivalence_of_comp_right H G
    change Scheme.fixedScalarDerivedModel X k
      ((H.mapHomologicalComplex (.up ℤ)).obj P) ≅ _
    exact (Scheme.fixedScalarProEtaleDerivedFactors X k
        ((H.mapHomologicalComplex (.up ℤ)).obj P)).symm ≪≫
      G.mapDerivedCategory.mapIso (H.mapDerivedCategoryFactors.app P).symm ≪≫
      (Functor.mapDerivedCategoryCompIso H G).app (DerivedCategory.Q.obj P) ≪≫
      HS.mapDerivedCategory.mapIso (DerivedCategory.Q.objObjPreimageIso _)
  obtain ⟨_, _, β, _⟩ := (IntegralConstantCompletion.integral_constant_completion l E X).2.2.2 0
  exact ⟨d₀.app ((restriction l E X).obj K) ≪≫
    (ConstantCompletion.extend q).mapIso (dφ.app K) ≪≫
    β.symm.app (EB.mapDerivedCategory.obj K) ≪≫
    (ConstantCompletion.extend p).mapIso (dB.app K).symm ≪≫ (dπ.app K').symm ≪≫ df.symm⟩

end AlgebraicGeometry.ProEtale.IntegralModelsStacks
