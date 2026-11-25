/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Bounded.BoundedConstructibleTowerSupplement
public import WeilConjectures.AlgebraicGeometry.CompletedConstantReduction.CompletedConstantSheafReductionSupplement
public import WeilConjectures.CategoryTheory.RingedSiteDerivedRestrictionUniverses
public import WeilConjectures.CategoryTheory.RingedSiteDerivedRestriction
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.AlgebraicGeometry.Integral.IntegralStratifiedPerfectModelsSupplement

import Mathlib.CategoryTheory.Adjunction.Additive
import all WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import all WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import all Mathlib.AlgebraicGeometry.Sites.Proetale
import all Mathlib.CategoryTheory.Sites.ConstantSheaf
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.AlgebraicGeometry.OpenImmersion
import all Mathlib.CategoryTheory.Sites.Over
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import all Mathlib.CategoryTheory.Sites.CoverLifting
import all WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import all WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
import WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionRingIsoSupplement
import WeilConjectures.AlgebraicGeometry.ProEtaleLocalRestriction.ProEtaleLocalDerivedRestrictionComparisonsSupplement
import WeilConjectures.CategoryTheory.Ringed.RingedDerivedRestrictionGeneralSupplement
import WeilConjectures.CategoryTheory.ConstantScalarRealization.ConstantRealizationDerivedScalarExtensionSupplement
import WeilConjectures.CategoryTheory.ConstantModuleFlat
import WeilConjectures.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor
import WeilConjectures.CategoryTheory.Site.SiteDerivedConstantModuleFunctor
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.RingTheory.Flat.Basic
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import Mathlib.LinearAlgebra.TensorProduct.Vanishing
import Mathlib.RingTheory.TensorProduct.DirectLimitFG
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.RingTheory.Flat.EquationalCriterion
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.CategoryTheory.Monoidal.Preadditive

/-! # Computing a perfect model before and after finite reduction

## References

* Bhatt--Scholze, Lemma 6.5.8(1), Proposition 6.6.11, local calculation
* Stacks Tags 06YS, 06YT, 06YU and 093J
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

-- `surjectiveTower_wEqualsLocallyBijective` leaves its coefficient universe free; pin it to `u + 1`
attribute [-instance] AlgebraicGeometry.ProEtale.surjectiveTower_wEqualsLocallyBijective

private instance proEtaleAbLocallyBijective (X : Scheme.{u}) :
    (ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  AlgebraicGeometry.ProEtale.surjectiveTower_wEqualsLocallyBijective.{u, 0} X

-- The localization proof uses only that U is weakly etale; no open-immersion
-- assumption enters the site equivalence or the module-adjunction comparison.
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private theorem chartModuleEquivalence {X : Scheme.{u}} (U : X.ProEt)
    (A : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :
    ∃ q : SheafOfModules.{u + 1}
        ((sheafCompose (ProEt.topology U.left)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
          ((proEtaleSheafInverseImage U.hom CommRingCat.{u + 1}).obj A)) ≌
          SheafOfModules.{u + 1} (((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj A).over U),
      Nonempty (proEtaleModuleInverseImage U.hom A ⋙ q.functor ≅
        SheafOfModules.overFunctor.{u + 1} ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj A) U) := by
  let R := (sheafCompose (ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj A
  let S := (sheafCompose (ProEt.topology U.left)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      ((proEtaleSheafInverseImage U.hom CommRingCat.{u + 1}).obj A)
  let G : U.left.ProEt ⥤ X.ProEt := MorphismProperty.Over.map ⊤ U.prop
  let : G.IsContinuous (ProEt.topology U.left) (ProEt.topology X) :=
    ProEt.isContinuous_overMap U.prop
  let : (MorphismProperty.Over.pullback @WeaklyEtale ⊤ U.hom).IsContinuous
      (ProEt.topology X) (ProEt.topology U.left) := ProEt.isContinuous_overPullback U.hom
  let a := MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ U.hom U.prop trivial
  let b := a.sheafPushforwardContinuous (E := CommRingCat.{u + 1})
    (ProEt.topology U.left) (ProEt.topology X)
  let c₀ := ((proEtaleSheafAdjunction U.hom CommRingCat.{u + 1}).leftAdjointUniq b).app A
  let c : S ≅ (G.sheafPushforwardContinuous RingCat.{u + 1}
      (ProEt.topology U.left) (ProEt.topology X)).obj R :=
    (sheafCompose (ProEt.topology U.left)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso c₀
  have := ProEt.sliceDense X U
  obtain ⟨q, hq⟩ := ProEt.module_transport ((ProEt.topology X).over U)
    (ProEt.topology U.left) (ProEt.sliceEquiv X U) (R.over U) S c
  let ψ : R ⟶ ((proEtaleBaseChange U.hom).sheafPushforwardContinuous
      RingCat.{u + 1} (ProEt.topology X) (ProEt.topology U.left)).obj S :=
    ⟨Functor.whiskerRight
      ((proEtaleSheafAdjunction U.hom CommRingCat.{u + 1}).unit.app A).hom
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩
  have H₁ : Functor.whiskerRight (NatTrans.op a.counit) R.obj =
      ψ.hom ≫ (proEtaleBaseChange U.hom).op.whiskerLeft c.hom.hom := by
    apply NatTrans.ext
    funext V
    have hc := Adjunction.unit_leftAdjointUniq_hom_app
      (proEtaleSheafAdjunction U.hom CommRingCat.{u + 1}) b A
    exact congrArg (fun f ↦ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).map
      (f.hom.app V)) hc.symm
  have H₂ : c.hom.hom ≫ G.op.whiskerLeft ψ.hom ≫
      Functor.whiskerRight (NatTrans.op a.unit) S.obj = 𝟙 S.obj := by
    apply NatTrans.ext
    funext V
    apply (cancel_mono (c.hom.hom.app V)).mp
    dsimp
    rw [Category.id_comp]
    have hn := c.hom.hom.naturality (a.unit.app V.unop).op
    dsimp at hn
    rw [Category.assoc, Category.assoc, hn]
    have hh := congrArg (fun t ↦ t.app (G.op.obj V)) H₁
    dsimp at hh
    erw [← Category.assoc (ψ.hom.app (G.op.obj V))
      (c.hom.hom.app ((proEtaleBaseChange U.hom).op.obj (G.op.obj V)))
      (R.obj.map (G.map (a.unit.app V.unop)).op), ← hh]
    rw [← Functor.map_comp, ← op_comp]
    erw [a.left_triangle_components]
    change c.hom.hom.app V ≫ R.obj.map (𝟙 (G.op.obj V)) = c.hom.hom.app V
    rw [R.obj.map_id]
    exact Category.comp_id (c.hom.hom.app V)
  let d := SheafOfModules.pushforwardPushforwardAdj a c.hom ψ H₁ H₂
  have z := proEtaleModuleInverseImageAdjunction U.hom A
  let z' : proEtaleModuleInverseImage U.hom A ⊣ SheafOfModules.pushforward.{u + 1} ψ :=
    z.ofNatIsoRight (SheafOfModules.pushforwardCongr (by
      simp [ψ, proEtaleRingDirectImageMap]))
  let e := z'.leftAdjointUniq d
  let t : SheafOfModules.overFunctor.{u + 1} R U ⋙ q.functor ≅
      SheafOfModules.pushforward.{u + 1} c.hom :=
    Functor.fullyFaithfulCancelRight (SheafOfModules.forget S) (eqToIso (by
      change SheafOfModules.overFunctor R U ⋙ (q.functor ⋙ SheafOfModules.forget S) = _
      rw [hq]
      rfl))
  refine ⟨q.symm, ⟨?_⟩⟩
  exact Functor.isoWhiskerRight (e ≪≫ t.symm) q.inverse ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (SheafOfModules.overFunctor R U) q.unitIso.symm ≪≫
    Functor.rightUnitor _

private def identityScalarPullIso {X Y : Scheme.{u}} (g : Y ⟶ X)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :
    proEtaleRingModulePullback g R ((adicTowerInverseImage g).obj R) (Iso.refl _) ≅
      proEtaleModuleInverseImage g R := by
  let R' := (adicTowerInverseImage g).obj R
  let θ := (SheafOfModules.exists_scalarExtensionRingIso.{u + 1, u, u + 1, 0}
    (Iso.refl R')).choose
  refine NatIso.ofComponents (fun M ↦ θ ((proEtaleModuleInverseImage g R).obj M)) ?_
  intro M N h
  exact (SheafOfModules.exists_scalarExtensionRingIso.{u + 1, u, u + 1, 0}
    (Iso.refl R')).choose_spec.2.2 _ _ ((proEtaleModuleInverseImage g R).map h)

private instance chartRestriction_additive (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) (U : X.ProEt) :
    (SheafOfModules.overFunctor.{u + 1} ((adicLisseForget X).obj R) U).Additive :=
  (ringedOverFunctor_exactGeneral.{u + 1, u, u + 1, u + 1}
    ((adicLisseForget X).obj R) U).1

private instance chartRestriction_limits (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) (U : X.ProEt) :
    PreservesFiniteLimits (SheafOfModules.overFunctor.{u + 1} ((adicLisseForget X).obj R) U) :=
  (ringedOverFunctor_exactGeneral.{u + 1, u, u + 1, u + 1}
    ((adicLisseForget X).obj R) U).2.1

private instance chartRestriction_colimits (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) (U : X.ProEt) :
    PreservesFiniteColimits (SheafOfModules.overFunctor.{u + 1} ((adicLisseForget X).obj R) U) :=
  (ringedOverFunctor_exactGeneral.{u + 1, u, u + 1, u + 1}
    ((adicLisseForget X).obj R) U).2.2

private def localRestrictionComparison {T S : Scheme.{u}} (g : S ⟶ T)
    (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1}) (U : S.ProEt)
    (K : DerivedCategory (pbcModules T R)) :
    (ringedDerivedRestrictionGeneral
      ((adicLisseForget S).obj ((adicTowerInverseImage g).obj R)) U).obj
        ((adicTowerPullback g R).obj K) ≅ integralLocalDerived g R U K := by
  let B := (adicLisseForget S).obj ((adicTowerInverseImage g).obj R)
  let F := SheafOfModules.overFunctor.{u + 1} B U
  have := (ringedOverFunctor_exactGeneral B U).1
  have := (ringedOverFunctor_exactGeneral B U).2.1
  have := (ringedOverFunctor_exactGeneral B U).2.2
  exact F.mapDerivedCategory.mapIso
    (DerivedCategory.Q.objObjPreimageIso ((adicTowerPullback g R).obj K)).symm ≪≫
      F.mapDerivedCategoryFactors.app _

private theorem chartDerivedEquivalence {X : Scheme.{u}} (U : X.ProEt)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :
    ∃ q : DerivedCategory (pbcModules U.left ((adicTowerInverseImage U.hom).obj R)) ≌
        DerivedCategory (SheafOfModules.{u + 1} (((adicLisseForget X).obj R).over U)),
      Nonempty (adicTowerPullback U.hom R ⋙ q.functor ≅
        ringedDerivedRestrictionGeneral ((adicLisseForget X).obj R) U) := by
  obtain ⟨q, ⟨e⟩⟩ := chartModuleEquivalence U R
  have : q.functor.Additive := Functor.additive_of_preserves_binary_products _
  have : q.inverse.Additive := Functor.additive_of_preserves_binary_products _
  let V := SheafOfModules.overFunctor.{u + 1} ((adicLisseForget X).obj R) U
  have : V.Additive := (ringedOverFunctor_exactGeneral _ U).1
  have : PreservesFiniteLimits V := (ringedOverFunctor_exactGeneral _ U).2.1
  have : PreservesFiniteColimits V := (ringedOverFunctor_exactGeneral _ U).2.2
  let e' := Functor.isoWhiskerRight (identityScalarPullIso U.hom R) q.functor ≪≫ e
  exact ⟨q.mapDerivedCategory,
    ⟨Functor.mapDerivedCategoryCompIso _ _ ≪≫ Functor.mapDerivedCategoryNatIso e'⟩⟩

private def scalarPullIso {X Y : Scheme.{u}} (g : Y ⟶ X)
    {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}} (φ : R ⟶ S) :
    pbcDerivedExtend φ ⋙ adicTowerPullback g S ≅
      adicTowerPullback g R ⋙ pbcDerivedExtend ((adicTowerInverseImage g).map φ) := by
  let R' := (adicTowerInverseImage g).obj R
  let S' := (adicTowerInverseImage g).obj S
  let φ' := (adicTowerInverseImage g).map φ
  let adjR := (proEtaleRingDerivedOperations_adjunction g R R' (Iso.refl _)).some
  let adjS := (proEtaleRingDerivedOperations_adjunction g S S' (Iso.refl _)).some
  let δ := proEtaleRingRestrictionDerivedDirectImage g R S R' S' φ φ'
    (Iso.refl _) (Iso.refl _) ((Category.id_comp _).trans (Category.comp_id _).symm)
  exact ((pbcDerivedScalarAdjunction φ).comp adjS).leftAdjointUniq
    ((adjR.comp (pbcDerivedScalarAdjunction φ')).ofNatIsoRight δ.symm)

private theorem scalarChartRespectsIso {X Y : Scheme.{u}} (g : Y ⟶ X)
    {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}} (φ : R ⟶ S)
    (U : Y.ProEt) {K L : DerivedCategory (pbcModules X R)}
    (e : Nonempty (integralLocalDerived g R U K ≅ integralLocalDerived g R U L)) :
    Nonempty (integralLocalDerived g S U ((pbcDerivedExtend φ).obj K) ≅
      integralLocalDerived g S U ((pbcDerivedExtend φ).obj L)) := by
  let Rg := (adicTowerInverseImage g).obj R
  let Sg := (adicTowerInverseImage g).obj S
  let φg := (adicTowerInverseImage g).map φ
  let φU := (adicTowerInverseImage U.hom).map φg
  obtain ⟨qR, ⟨eR⟩⟩ := chartDerivedEquivalence U Rg
  obtain ⟨qS, ⟨eS⟩⟩ := chartDerivedEquivalence U Sg
  obtain ⟨e⟩ := e
  let a := qR.fullyFaithfulFunctor.preimageIso
    (eR.app ((adicTowerPullback g R).obj K) ≪≫
      localRestrictionComparison g R U K ≪≫ e ≪≫
        (localRestrictionComparison g R U L).symm ≪≫
          (eR.app ((adicTowerPullback g R).obj L)).symm)
  let c (M : DerivedCategory (pbcModules X R)) :=
    qS.functor.mapIso
      ((adicTowerPullback U.hom Sg).mapIso ((scalarPullIso g φ).app M) ≪≫
        (scalarPullIso U.hom φg).app ((adicTowerPullback g R).obj M))
  let t (M : DerivedCategory (pbcModules X R)) :=
    (localRestrictionComparison g S U ((pbcDerivedExtend φ).obj M)).symm ≪≫
      (eS.app ((adicTowerPullback g S).obj ((pbcDerivedExtend φ).obj M))).symm ≪≫ c M
  exact ⟨t K ≪≫ qS.functor.mapIso ((pbcDerivedExtend φU).mapIso a) ≪≫ (t L).symm⟩

private instance proEt_small (X : Scheme.{u}) : EssentiallySmall.{u + 1} X.ProEt :=
  essentiallySmallSelf.{0, u, u + 1} _

private theorem constant_kflat (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (C : CochainComplex (ModuleCat.{u + 1} A) ℤ) (b : ℤ) [C.IsStrictlyLE b]
    (hC : ∀ q, Module.Projective A (C.X q)) :
    CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (R := adicLisseConstantRing X A)
      ((CompletedConstantReduction.constantComplex X A).obj C) := by
  let F := adicLisseConstantModules X A
  have : F.Additive := CompletedConstantReduction.constant_additive X A
  have : ((CompletedConstantReduction.constantComplex X A).obj C).IsStrictlyLE b :=
    (CochainComplex.isStrictlyLE_iff _ b).2 fun q hq ↦
      F.map_isZero (C.isZero_of_isStrictlyLE b q hq)
  apply SheafOfModules.isKFlatIndependentCoefficients_of_boundedAbove_flatOnSite.{u + 1, u, u + 1}
    (adicLisseConstantRing X A) _ b
  intro q
  have : Module.Projective A (C.X q) := hC q
  exact isFlatOnSite_constantModule.{u + 1, u} (ProEt.topology X) A (C.X q) inferInstance

private def integralMapLocalIso {X Y : Scheme.{u}} (g : Y ⟶ X)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) (U : Y.ProEt)
    {K L : DerivedCategory (pbcModules X R)} (e : K ≅ L) :
    integralLocalDerived g R U K ≅ integralLocalDerived g R U L :=
  (localRestrictionComparison g R U K).symm ≪≫
    (ringedDerivedRestrictionGeneral
      ((adicLisseForget Y).obj ((adicTowerInverseImage g).obj R)) U).mapIso
        ((adicTowerPullback g R).mapIso e) ≪≫ localRestrictionComparison g R U L

private def restrictIsoAsExtend {X : Scheme.{u}}
    {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}} (j : R ≅ S) :
    pbcDerivedRestrict j.hom ≅ pbcDerivedExtend j.inv := by
  let e := proEtaleScalarEquivalence X ((adicLisseForget X).mapIso j)
  have : e.functor.Additive := inferInstanceAs (pbcRestrict j.hom).Additive
  have : e.inverse.Additive := inferInstanceAs (pbcRestrict j.inv).Additive
  have adj : pbcDerivedRestrict j.hom ⊣ pbcDerivedRestrict j.inv :=
    e.mapDerivedCategory.toAdjunction
  exact adj.leftAdjointUniq (pbcDerivedScalarAdjunction j.inv)

private def constantTensorIso (X : Scheme.{u})
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (q : A →+* B)
    (C : CochainComplex (ModuleCat.{u + 1} A) ℤ) (b : ℤ) [C.IsStrictlyLE b]
    (hC : ∀ n, Module.Projective A (C.X n)) :
    letI := (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1} q).left_adjoint_additive
    (pbcDerivedExtend ((constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
      (CommRingCat.ofHom q))).obj
        (DerivedCategory.Q.obj ((CompletedConstantReduction.constantComplex X A).obj C)) ≅
      DerivedCategory.Q.obj ((CompletedConstantReduction.constantComplex X B).obj
        (((ModuleCat.extendScalars q).mapHomologicalComplex (.up ℤ)).obj C)) := by
  letI := (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1} q).left_adjoint_additive
  let J := ProEt.topology X
  let φ := (constantSheaf J CommRingCat.{u + 1}).map (CommRingCat.ofHom q)
  let C₀ := (CompletedConstantReduction.constantComplex X A).obj C
  have : IsIso (pbcComplexCounit φ C₀) := by
    have := pbcExtensionCounit_isIso φ C₀ (constant_kflat X C b hC)
    dsimp only [pbcComplexCounit]
    infer_instance
  let e := (pbcScalarAdjunction φ).leftAdjointUniq
    (CategoryTheory.ConstantScalarRealization.adjunction J q)
  have (n : ℤ) : IsIso
      ((CategoryTheory.ConstantScalarRealization.complexComparison J q C).f n) :=
    (CategoryTheory.ConstantScalarRealization.moduleComparison_tensor J q (C.X n)).1
  have : IsIso (CategoryTheory.ConstantScalarRealization.complexComparison J q C) :=
    HomologicalComplex.Hom.isIso_of_components _
  exact asIso (pbcComplexCounit φ C₀) ≪≫ DerivedCategory.Q.mapIso
    ((NatIso.mapHomologicalComplex e (.up ℤ)).app C₀ ≪≫
      asIso (CategoryTheory.ConstantScalarRealization.complexComparison J q C))

/-- Finite reduction of a perfect completed model on a chart is computed termwise. -/
theorem perfect_chart_tensor_comparison
    {X Y : Scheme.{u}} (g : Y ⟶ X) [IsImmersion g]
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (K : d.derived X) (U : Y.ProEt)
    (C : CochainComplex (ModuleCat.{u + 1} A) ℤ) (a b : ℤ)
    (_ha : C.IsStrictlyGE a) (hb : C.IsStrictlyLE b)
    (hC : ∀ q, Module.Projective A (C.X q) ∧ Module.Finite A (C.X q))
    (e : Nonempty (integralLocalDerived g (d.completedRing X) U K ≅
      integralLocalDerived g (d.completedRing X) U
        ((pbcDerivedExtend (CompletedConstantReduction.base X d.ideal ≫
          (pbcCompletedComparison X d).hom)).obj
            (DerivedCategory.Q.obj ((CompletedConstantReduction.constantComplex X A).obj C))))) :
    ∀ n,
      letI := (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1}
        (Ideal.Quotient.mk (d.ideal ^ (n + 1)))).left_adjoint_additive
      Nonempty (integralLocalDerived g
      (adicLisseConstantRing X (A ⧸ d.ideal ^ (n + 1))) U
        ((pbcDerivedRestrict (pbcLevelConstantComparison X d n).hom).obj
          ((d.reduction X n).obj K)) ≅
      integralLocalDerived g (adicLisseConstantRing X (A ⧸ d.ideal ^ (n + 1))) U
        (DerivedCategory.Q.obj
          ((CompletedConstantReduction.constantComplex X (A ⧸ d.ideal ^ (n + 1))).obj
            (((ModuleCat.extendScalars.{u + 1, u + 1, u + 1} (Ideal.Quotient.mk
              (d.ideal ^ (n + 1)))).mapHomologicalComplex (.up ℤ)).obj C)))) := by
  classical
  intro n
  let := (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1}
    (Ideal.Quotient.mk (d.ideal ^ (n + 1)))).left_adjoint_additive
  let := hb
  let c := CompletedConstantReduction.base X d.ideal ≫ (pbcCompletedComparison X d).hom
  let p := pbcAdicProjection X d n
  let j := pbcLevelConstantComparison X d n
  let q := Ideal.Quotient.mk (d.ideal ^ (n + 1))
  let β := (constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
    (CommRingCat.ofHom q)
  let C₀ := DerivedCategory.Q.obj ((CompletedConstantReduction.constantComplex X A).obj C)
  have hcp : c ≫ p = β ≫ j.hom := by
    dsimp [c, p, pbcAdicProjection, pbcCompletedComparison]
    rw [Category.assoc, HasLimit.isoOfNatIso_hom_π, ← Category.assoc]
    have hb₀ := (CompletedConstantReduction.base_exists X d.ideal).choose_spec.1 n
    change CompletedConstantReduction.base X d.ideal ≫ _ = _ at hb₀
    rw [hb₀]
    rfl
  have hcpj : c ≫ p ≫ j.inv = β := by
    rw [← Category.assoc, hcp, Category.assoc, j.hom_inv_id, Category.comp_id]
  obtain ⟨eraw⟩ := scalarChartRespectsIso g p U e
  let enorm := restrictIsoAsExtend j
  have en : Nonempty (integralLocalDerived g _ U
      ((pbcDerivedRestrict j.hom).obj ((pbcDerivedExtend p).obj K)) ≅
      integralLocalDerived g _ U
        ((pbcDerivedRestrict j.hom).obj
          ((pbcDerivedExtend p).obj ((pbcDerivedExtend c).obj C₀)))) := by
    obtain ⟨et⟩ := scalarChartRespectsIso g j.inv U ⟨eraw⟩
    exact ⟨integralMapLocalIso g _ U (enorm.app _) ≪≫ et ≪≫
      (integralMapLocalIso g _ U (enorm.app _)).symm⟩
  obtain ⟨en⟩ := en
  let assoc₁ := pbcReductionNormalization c p (c ≫ p) rfl C₀
  let assoc₂ := pbcReductionNormalization (c ≫ p) j.inv β hcpj C₀
  let eglobal := enorm.app _ ≪≫ (pbcDerivedExtend j.inv).mapIso assoc₁ ≪≫ assoc₂ ≪≫
    constantTensorIso X q C b (fun i ↦ (hC i).1)
  exact ⟨en ≪≫ integralMapLocalIso g _ U eglobal⟩

end AlgebraicGeometry.Scheme
