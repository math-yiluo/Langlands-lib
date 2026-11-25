/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientFiniteRealization
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientUnitPush
import WeilConjectures.CategoryTheory.Adjunction.SmoothPurity.RightDerivedSingleCounit
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Finite.DiagonalFiniteConstantPullbackComparison

/-! # The finite constant coefficient adjunct in degree zero -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
-- The derived comparison APIs use the standard sheaf Abelian structure.
attribute [-instance] AlgebraicGeometry.ProEtale.diagonalModuleSheafAbelian
  AlgebraicGeometry.ProEtale.diagonalAbSheafAbelian in
section
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open MonObj
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

attribute [local irreducible] Functor.mapDerivedCategory Functor.leftDerivedFunctor
  HasDerivedCategory.ofIsGrothendieckAbelian
  Functor.rightDerivedFunctor Functor.rightDerivedFunctorUnitQ finiteConstantAbComparison
  finiteUnitComparison

private theorem ab_comparison_constants (A : Type (u + 1)) [CommRing A]
    (X : Scheme.{u}) (T : X.ProEtᵒᵖ) :
    (forget₂ (ModuleCat.{u + 1} A) Ab.{u + 1}).map
        ((toSheafify (Scheme.ProEt.topology X)
          ((Functor.const X.ProEtᵒᵖ).obj (ModuleCat.of A A))).app T) ≫
      (finiteConstantAbComparison A X).hom.hom.app T =
    (toSheafify (Scheme.ProEt.topology X)
      ((Functor.const X.ProEtᵒᵖ).obj (AddCommGrpCat.of A))).app T := by
  let : (Scheme.ProEt.topology X).PreservesSheafification
      (forget₂ (ModuleCat.{u + 1} A) Ab.{u + 1}) :=
    Sheaf.preservesSheafification_of_adjunction (Scheme.ProEt.topology X)
      (ModuleCat.forget₂CoinduceAdj A)
  let V := forget₂ (ModuleCat.{u + 1} A) Ab.{u + 1}
  have h := sheafComposeIso_inv_fac (Scheme.ProEt.topology X) V
    ((Functor.const X.ProEtᵒᵖ).obj (ModuleCat.of A A))
  have hn := toSheafify_naturality (Scheme.ProEt.topology X)
    (Functor.constComp X.ProEtᵒᵖ (ModuleCat.of A A) V).hom
  have he := congrArg (fun k ↦ k ≫ sheafifyMap (Scheme.ProEt.topology X)
    (Functor.constComp X.ProEtᵒᵖ (ModuleCat.of A A) V).hom) h
  rw [Category.assoc, ← hn] at he
  have he' := congrArg (fun k ↦ k.app T) he
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.constComp_hom_app,
    Category.id_comp] at he'
  unfold finiteConstantAbComparison
  change V.map _ ≫ ((constantCommuteCompose (Scheme.ProEt.topology X) V).hom.app
    (ModuleCat.of A A)).hom.app T = _
  rw [constantCommuteCompose_hom_app_hom]
  exact he'

private theorem constant_one_presheaf (A : Type (u + 1)) [CommRing A]
    (X : Scheme.{u}) :
    Functor.LaxMonoidal.ε (sheafToPresheaf (Scheme.ProEt.topology X) Ab.{u + 1}) ≫
        (@MonObj.one _ _ _ (finiteConstantAbRing A X)
          ((sfbConstantRing X).obj (RingCat.of A)).mon).hom =
      (Functor.const X.ProEtᵒᵖ).map (η[AddCommGrpCat.of A]) ≫
        toSheafify (Scheme.ProEt.topology X)
          ((Functor.const X.ProEtᵒᵖ).obj (AddCommGrpCat.of A)) := by
  have hu : (@MonObj.one _ _ _ (finiteConstantAbRing A X)
      ((sfbConstantRing X).obj (RingCat.of A)).mon) =
      (constantSheaf (Scheme.ProEt.topology X) Ab.{u + 1}).map
        (η[AddCommGrpCat.of A]) := by
    change Functor.LaxMonoidal.ε (constantSheaf (Scheme.ProEt.topology X) Ab.{u + 1}) ≫
      (constantSheaf (Scheme.ProEt.topology X) Ab.{u + 1}).map
        (η[AddCommGrpCat.of A]) = _
    have he : Functor.LaxMonoidal.ε
        (constantSheaf (Scheme.ProEt.topology X) Ab.{u + 1}) = 𝟙 _ := by
      change (𝟙 _) ≫ (presheafToSheaf (Scheme.ProEt.topology X) Ab.{u + 1}).map
        (𝟙 _) = _
      erw [CategoryTheory.Functor.map_id, Category.id_comp]
      rfl
    rw [he, Category.id_comp]
  rw [hu]
  change toSheafify (Scheme.ProEt.topology X)
      ((Functor.const X.ProEtᵒᵖ).obj (𝟙_ Ab.{u + 1})) ≫
    ((constantSheaf (Scheme.ProEt.topology X) Ab.{u + 1}).map (η[AddCommGrpCat.of A])).hom = _
  exact (toSheafify_naturality (Scheme.ProEt.topology X)
    ((Functor.const X.ProEtᵒᵖ).map (η[AddCommGrpCat.of A]))).symm

private theorem ordinary_map_of_one
    (A : Type (u + 1)) [CommRing A] (Y : Scheme.{u})
    (m : geoCartierConstant A Y ⟶
      (lowerStar (ModuleCat.{u + 1} A) (ProjectiveLine Y ↘ Y)).obj
        (geoCartierConstant A (ProjectiveLine Y)))
    (h : (@MonObj.one _ _ _ (finiteConstantAbRing A Y)
        ((sfbConstantRing Y).obj (RingCat.of A)).mon) ≫ (finiteConstantAbComparison A Y).inv ≫
        (sheafCompose (Scheme.ProEt.topology Y)
          (forget₂ (ModuleCat.{u + 1} A) Ab.{u + 1})).map m ≫
        (lowerStar Ab.{u + 1} (ProjectiveLine Y ↘ Y)).map
          (finiteConstantAbComparison A (ProjectiveLine Y)).hom =
      Functor.LaxMonoidal.ε (lowerStar Ab.{u + 1} (ProjectiveLine Y ↘ Y)) ≫
        (lowerStar Ab.{u + 1} (ProjectiveLine Y ↘ Y)).map
          (@MonObj.one _ _ _ (finiteConstantAbRing A (ProjectiveLine Y))
        ((sfbConstantRing (ProjectiveLine Y)).obj (RingCat.of A)).mon)) :
    m = Scheme.proEtaleConstantDirectImageMap (ProjectiveLine Y ↘ Y)
      (ModuleCat.{u + 1} A) (ModuleCat.of A A) := by
  let X := ProjectiveLine Y
  let f := ProjectiveLine Y ↘ Y
  let U := forget₂ (ModuleCat.{u + 1} A) Ab.{u + 1}
  let F := Scheme.proEtaleBaseChange f
  let J := Scheme.ProEt.topology Y
  let K := Scheme.ProEt.topology X
  let cY := finiteConstantAbComparison A Y
  let cX := finiteConstantAbComparison A X
  let tY := toSheafify J ((Functor.const Y.ProEtᵒᵖ).obj (ModuleCat.of A A))
  let tX := toSheafify K ((Functor.const X.ProEtᵒᵖ).obj (ModuleCat.of A A))
  let aY := toSheafify J ((Functor.const Y.ProEtᵒᵖ).obj (AddCommGrpCat.of A))
  let aX := toSheafify K ((Functor.const X.ProEtᵒᵖ).obj (AddCommGrpCat.of A))
  let eY := Functor.LaxMonoidal.ε (sheafToPresheaf J Ab.{u + 1})
  let eX := Functor.LaxMonoidal.ε (sheafToPresheaf K Ab.{u + 1})
  let oY := @MonObj.one _ _ _ (finiteConstantAbRing A Y)
    ((sfbConstantRing Y).obj (RingCat.of A)).mon
  let oX := @MonObj.one _ _ _ (finiteConstantAbRing A X)
    ((sfbConstantRing X).obj (RingCat.of A)).mon
  have hn : tY ≫ m.hom = Functor.whiskerLeft F.op tX := by
    apply NatTrans.ext
    funext T
    apply ModuleCat.hom_ext
    apply LinearMap.ext_ring
    have hone : (η[AddCommGrpCat.of A]) (ULift.up (1 : ℤ)) = (1 : A) := by
      change ((1 : ℤ) : A) = 1
      exact Int.cast_one
    have hcY := ab_comparison_constants A Y T
    have hcX := ab_comparison_constants A X (F.op.obj T)
    have hy : (eY.app T ≫ oY.hom.app T) (ULift.up (1 : ℤ)) = aY.app T (1 : A) := by
      have hh := ConcreteCategory.congr_hom (congr_app (constant_one_presheaf A Y) T)
        (ULift.up (1 : ℤ))
      simp only [NatTrans.comp_app, ConcreteCategory.comp_apply, Functor.const_map_app] at hh
      change oY.hom.app T (eY.app T (ULift.up (1 : ℤ))) =
        aY.app T ((η[AddCommGrpCat.of A]) (ULift.up (1 : ℤ))) at hh
      exact hh.trans (congrArg (fun z ↦ aY.app T z) hone)
    have hx : (eX.app (F.op.obj T) ≫ oX.hom.app (F.op.obj T))
        (ULift.up (1 : ℤ)) = aX.app (F.op.obj T) (1 : A) := by
      have hh := ConcreteCategory.congr_hom
        (congr_app (constant_one_presheaf A X) (F.op.obj T)) (ULift.up (1 : ℤ))
      simp only [NatTrans.comp_app, ConcreteCategory.comp_apply, Functor.const_map_app] at hh
      change oX.hom.app (F.op.obj T) (eX.app (F.op.obj T) (ULift.up (1 : ℤ))) =
        aX.app (F.op.obj T) ((η[AddCommGrpCat.of A]) (ULift.up (1 : ℤ))) at hh
      exact hh.trans (congrArg (fun z ↦ aX.app (F.op.obj T) z) hone)
    have hε := Functor.ε_sheafToPresheaf_app_comp_ε_sheafPushforwardContinuous_app
      F Ab.{u + 1} J K T
    have hh := congrArg (fun k ↦ eY.app T ≫ k.hom.app T) h
    change eY.app T ≫ oY.hom.app T ≫ cY.inv.hom.app T ≫
        U.map (m.hom.app T) ≫ cX.hom.hom.app (F.op.obj T) =
      eY.app T ≫ (Functor.LaxMonoidal.ε (lowerStar Ab.{u + 1} f)).hom.app T ≫
        oX.hom.app (F.op.obj T) at hh
    erw [reassoc_of% hε] at hh
    have hh1 := ConcreteCategory.congr_hom hh (ULift.up (1 : ℤ))
    simp only [ConcreteCategory.comp_apply] at hh1 hy hx
    rw [hy] at hh1
    erw [hx] at hh1
    have hcy := ConcreteCategory.congr_hom hcY (1 : A)
    have hcx := ConcreteCategory.congr_hom hcX (1 : A)
    simp only [ConcreteCategory.comp_apply] at hcy hcx
    have hinv : cY.inv.hom.app T (aY.app T (1 : A)) = tY.app T (1 : A) := by
      erw [← hcy]
      change cY.inv.hom.app T (cY.hom.hom.app T (tY.app T (1 : A))) = _
      have hh := ConcreteCategory.congr_hom
        (congrArg (fun k ↦ k.hom.app T) cY.hom_inv_id) (tY.app T (1 : A))
      simpa only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
        ConcreteCategory.comp_apply, ObjectProperty.FullSubcategory.id_hom,
        NatTrans.id_app, ConcreteCategory.id_apply] using hh
    erw [hinv, ← hcx] at hh1
    exact (ConcreteCategory.bijective_of_isIso (cX.hom.hom.app (F.op.obj T))).1 hh1
  apply ((sheafificationAdjunction J (ModuleCat.{u + 1} A)).homEquiv _ _).injective
  unfold Scheme.proEtaleConstantDirectImageMap
  erw [Equiv.apply_symm_apply]
  exact hn

private theorem single_unitQ {C D : Type*} [Category C] [Category D]
    [Abelian C] [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D]
    [Abelian.HasKInjectiveResolutions C] (R : C ⥤ D) [R.Additive] (M : C) :
    R.singleRightDerivedUnit.app M =
      DerivedCategory.Q.map
        ((HomologicalComplex.singleMapHomologicalComplex R (.up ℤ) 0).inv.app M) ≫
      R.rightDerivedFunctorUnitQ ((HomologicalComplex.single C (.up ℤ) 0).obj M) := by
  rw [Functor.singleRightDerivedUnit_app]
  unfold Functor.rightDerivedFunctorUnitQ
  have hq (K : CochainComplex C ℤ) :
      (DerivedCategory.quotientCompQhIso C).hom.app K = 𝟙 _ := rfl
  have hqi (K : CochainComplex D ℤ) :
      (DerivedCategory.quotientCompQhIso D).inv.app K = 𝟙 _ := rfl
  simp only [hq, hqi, Category.id_comp]
  erw [R.rightDerivedFunctor.map_id, Category.comp_id]
  rfl

section DerivedAdjunct

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D] [Abelian.HasKInjectiveResolutions D]
  {L : C ⥤ D} {R : D ⥤ C} [L.Additive] [R.Additive]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  [MonoidalCategory C] [MonoidalPreadditive C]
  [HasCountableCoproducts C]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [HasColimitsOfShape ℤ C] [HasExactColimitsOfShape ℤ C]
  [∀ (X : C), PreservesColimitsOfShape ℤ ((curriedTensor C).obj X)]
  [∀ (X : C), PreservesColimitsOfShape ℤ ((curriedTensor C).flip.obj X)]
  [Abelian.HasFunctorialFlatResolution C]

private theorem derived_single_adjunct (a : L ⊣ R) {M : C} {N : D}
    (m : M ⟶ R.obj N) :
    (DerivedCategory.singleFunctor _ 0).map m ≫ R.singleRightDerivedUnit.app N =
      a.derivedAdjunction.homEquiv _ _
        ((Functor.compIsoApp L.singleFunctorCompLeftDerivedFunctorIso M).hom ≫
          (DerivedCategory.singleFunctor _ 0).map ((a.homEquiv _ _).symm m)) := by
  let e := L.leftDerivedFunctorIsoMapDerivedCategory
  let b := a.derivedAdjunction.ofNatIsoLeft e
  have hc := Adjunction.single_rightDerived_counit a N
  have hm : (DerivedCategory.singleFunctor _ 0).map m ≫ R.singleRightDerivedUnit.app N =
      b.homEquiv _ _ ((L.mapDerivedCategorySingleFunctor 0).hom.app M ≫
        (DerivedCategory.singleFunctor _ 0).map ((a.homEquiv _ _).symm m)) := by
    apply (b.homEquiv _ _).symm.injective
    rw [Equiv.symm_apply_apply, b.homEquiv_counit, Functor.map_comp, Category.assoc]
    erw [hc, (L.mapDerivedCategorySingleFunctor 0).hom.naturality_assoc m]
    simp only [Functor.comp_map, ← Functor.map_comp, a.homEquiv_counit]
  rw [Adjunction.homEquiv_ofNatIsoLeft_apply] at hm
  simpa only [Functor.compIsoApp, Iso.app_hom,
    Functor.singleFunctorCompLeftDerivedFunctorIso, Iso.trans_hom,
    NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Functor.comp_obj, Category.assoc] using hm

private theorem derived_adjunct_transport (a : L ⊣ R) {M : C} {N : D}
    (m : M ⟶ R.obj N) {P : DerivedCategory C} {Q : DerivedCategory D}
    (c : P ≅ (DerivedCategory.singleFunctor C 0).obj M)
    (d : Q ≅ (DerivedCategory.singleFunctor D 0).obj N)
    (g : L.leftDerivedFunctor.obj P ⟶ Q)
    (hg : g ≫ d.hom = L.leftDerivedFunctor.map c.hom ≫
      (Functor.compIsoApp L.singleFunctorCompLeftDerivedFunctorIso M).hom ≫
        (DerivedCategory.singleFunctor D 0).map ((a.homEquiv _ _).symm m)) :
    (DerivedCategory.singleFunctor C 0).map m ≫
      DerivedCategory.Q.map
        ((HomologicalComplex.singleMapHomologicalComplex R (.up ℤ) 0).inv.app N) ≫
      R.rightDerivedFunctorUnitQ ((HomologicalComplex.single D (.up ℤ) 0).obj N) ≫
      R.rightDerivedFunctor.map d.inv = c.inv ≫ a.derivedAdjunction.homEquiv _ _ g := by
  have hn : ((Functor.compIsoApp L.singleFunctorCompLeftDerivedFunctorIso M).hom ≫
      (DerivedCategory.singleFunctor D 0).map ((a.homEquiv _ _).symm m)) ≫ d.inv =
    L.leftDerivedFunctor.map c.inv ≫ g := by
    apply (cancel_mono d.hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [hg]
    simp only [← Functor.map_comp_assoc, Iso.inv_hom_id,
      CategoryTheory.Functor.map_id, Category.id_comp]
  have ht := congrArg (fun k ↦ a.derivedAdjunction.homEquiv _ _ k) hn
  rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_naturality_left,
    ← derived_single_adjunct a m] at ht
  simpa only [single_unitQ, Category.assoc] using ht

end DerivedAdjunct

private theorem ordinary_constant_map_unit (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Scheme.proEtaleConstantDirectImageMap f (ModuleCat.{u + 1} A) (ModuleCat.of A A) =
      Functor.LaxMonoidal.ε (lowerStar (ModuleCat.{u + 1} A) f) := by
  apply ((sheafificationAdjunction (Scheme.ProEt.topology Y)
    (ModuleCat.{u + 1} A)).homEquiv _ _).injective
  rw [Scheme.proEtaleConstantDirectImageMap, Equiv.apply_symm_apply]
  change _ = toSheafify (Scheme.ProEt.topology Y)
    ((Functor.const Y.ProEtᵒᵖ).obj (ModuleCat.of A A)) ≫
      (Functor.LaxMonoidal.ε (lowerStar (ModuleCat.{u + 1} A) f)).hom
  apply NatTrans.ext
  funext T
  exact (Functor.ε_sheafToPresheaf_app_comp_ε_sheafPushforwardContinuous_app
    (Scheme.proEtaleBaseChange f) (ModuleCat.{u + 1} A)
      (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X) T).symm

/-- A unital map from the constant rank-one module to its ordinary direct image
represents the canonical finite unit adjunct after the single-complex and finite
constant comparisons. Source: diagonal tower coefficient changes (1), ordinary
constant units and the canonical derived adjunction.
(blueprint: lem-diagonal-finite-constant-adjunct).

Proof: the constant-sheaf adjunction identifies maps out of the constant rank-one
module with module maps out of A on terminal sections. Such a module map is determined
by the image of one. The hypothesis identifies that image with constant one on the
projective line, so m is the adjunct of the canonical constant-sheaf pullback
isomorphism. The canonical derived adjunction, evaluated on the single complex,
is the single of this ordinary adjunct followed by the right-derived unit. This
follows from the derived counit factorization and the ordinary triangle identity.
Finally the comparison inverse image and both geometric inverse images preserve
constant sheaves by uniqueness of their left adjoints to sections. Naturality and
uniqueness of these left-adjoint comparisons identify the constant pullback just
used with geoP1UnitPullback under finiteUnitComparison. Substituting this identity
into the derived hom-equivalence proves the equation. These arguments also apply
on the empty scheme and over the zero ring. -/
theorem finite_constant_adjunct_of_one
    (A : Type (u + 1)) [CommRing A] (Y : Scheme.{u})
    (m : geoCartierConstant A Y ⟶
      (lowerStar (ModuleCat.{u + 1} A) (ProjectiveLine Y ↘ Y)).obj
        (geoCartierConstant A (ProjectiveLine Y)))
    (h : (@MonObj.one _ _ _ (finiteConstantAbRing A Y)
        ((sfbConstantRing Y).obj (RingCat.of A)).mon) ≫ (finiteConstantAbComparison A Y).inv ≫
        (sheafCompose (Scheme.ProEt.topology Y)
          (forget₂ (ModuleCat.{u + 1} A) Ab.{u + 1})).map m ≫
        (lowerStar Ab.{u + 1} (ProjectiveLine Y ↘ Y)).map
          (finiteConstantAbComparison A (ProjectiveLine Y)).hom =
      Functor.LaxMonoidal.ε (lowerStar Ab.{u + 1} (ProjectiveLine Y ↘ Y)) ≫
        (lowerStar Ab.{u + 1} (ProjectiveLine Y ↘ Y)).map
          (@MonObj.one _ _ _ (finiteConstantAbRing A (ProjectiveLine Y))
        ((sfbConstantRing (ProjectiveLine Y)).obj (RingCat.of A)).mon)) :
    (DerivedCategory.singleFunctor _ 0).map m ≫
      DerivedCategory.Q.map
        ((HomologicalComplex.singleMapHomologicalComplex
          (lowerStar (ModuleCat.{u + 1} A) (ProjectiveLine Y ↘ Y))
          (.up ℤ) 0).inv.app (geoCartierConstant A (ProjectiveLine Y))) ≫
      (lowerStar (ModuleCat.{u + 1} A) (ProjectiveLine Y ↘ Y)).rightDerivedFunctorUnitQ
        ((HomologicalComplex.single _ (.up ℤ) 0).obj
          (geoCartierConstant A (ProjectiveLine Y))) ≫
      (geoP1Pushforward A (ProjectiveLine Y ↘ Y)).map
        (finiteUnitComparison A (ProjectiveLine Y)).inv =
    (finiteUnitComparison A Y).inv ≫ finiteUnitAdjunct A Y := by
  have hm : m = Functor.LaxMonoidal.ε
      (lowerStar (ModuleCat.{u + 1} A) (ProjectiveLine Y ↘ Y)) :=
    (ordinary_map_of_one A Y m h).trans (ordinary_constant_map_unit A (ProjectiveLine Y ↘ Y))
  have ha : ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A)
      (ProjectiveLine Y ↘ Y)).homEquiv _ _).symm m = Functor.OplaxMonoidal.η
        (upperStar (ModuleCat.{u + 1} A) (ProjectiveLine Y ↘ Y)) := by
    apply ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A)
      (ProjectiveLine Y ↘ Y)).homEquiv _ _).injective
    rw [Equiv.apply_symm_apply, hm, Adjunction.homEquiv_unit]
    exact (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A)
      (ProjectiveLine Y ↘ Y)).unit_app_unit_comp_map_η.symm
  have hc : (geoP1UnitPullback A (ProjectiveLine Y ↘ Y)).hom ≫
      (finiteUnitComparison A (ProjectiveLine Y)).hom =
      (upperStar (ModuleCat.{u + 1} A) (ProjectiveLine Y ↘ Y)).leftDerivedFunctor.map
        (finiteUnitComparison A Y).hom ≫
      (Functor.compIsoApp
        (upperStar (ModuleCat.{u + 1} A)
          (ProjectiveLine Y ↘ Y)).singleFunctorCompLeftDerivedFunctorIso
        (geoCartierConstant A Y)).hom ≫
      (DerivedCategory.singleFunctor _ 0).map
        (((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A)
          (ProjectiveLine Y ↘ Y)).homEquiv _ _).symm m) := by
    rw [ha]
    exact finite_constant_pullback_comparison A (ProjectiveLine Y ↘ Y)
  unfold finiteUnitAdjunct geoP1Pushforward derivedUpperStarLowerStarAdjunction
  exact derived_adjunct_transport
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) (ProjectiveLine Y ↘ Y)) m
    (finiteUnitComparison A Y) (finiteUnitComparison A (ProjectiveLine Y))
    (geoP1UnitPullback A (ProjectiveLine Y ↘ Y)).hom hc

end AlgebraicGeometry.ProEtale.DiagonalCoefficients

end
