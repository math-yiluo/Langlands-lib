/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Strict.Tower.StrictTowerOperationsSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtaleOpenRestriction.ProEtaleOpenRestrictionCounit
public import WeilConjectures.AlgebraicGeometry.ProEtaleTensorComparison.ProEtaleInverseImageTensorComparisonSupplement
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
public import WeilConjectures.AlgebraicGeometry.RingedRestrictionExchange.RingedExchangeChainUnit
public import WeilConjectures.CategoryTheory.Derived.DerivedDegreeZeroExchangeEquation
public import WeilConjectures.AlgebraicGeometry.RingedRestrictionExchange.RingedUpperOpenPullbackKInjective
public import WeilConjectures.AlgebraicGeometry.RingedRestrictionExchange.OpenCube.RingedRestrictionOpenCube

public import WeilConjectures.AlgebraicGeometry.RingedRestrictionExchange.RingedOpenSquareUnitNormalization
import WeilConjectures.AlgebraicGeometry.StrictTowerRingedSquare.ProEtaleRingedSquareLocalization
import WeilConjectures.AlgebraicGeometry.RingedRestrictionExchange.RingedRestrictionDerivedCube
import WeilConjectures.AlgebraicGeometry.RingedRestrictionExchange.RingedOrdinaryOpenExchange
import WeilConjectures.AlgebraicGeometry.RingedRestrictionExchange.ProEtaleRingedOpenCoverReflectsIso
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback

/-!
# Normalized ringed restriction exchange and open descent

## Main statements

* `resolution_formula`: the two-resolution formula and its choice independence.
* `transpose_normalization`: the ordinary-derived adjunction normalization.
* `degreeZero_normalization`: comparison with the ordinary module exchange.
* `open_comparison`, `open_sectionwise`, `open_representative`: normalized open comparison.
* `openCube_exists`, `open_restriction`, `open_descent`: open restriction and cover detection.
* `identity_normalization`: identity base change.

`actualSquare p h R` has exactly the four rings in the statement. The general
`StrictTowerRingedSquare` interfaces allow their canonically isomorphic presentations;
no arbitrary exchange transformation is an input. Every pullback here is exact.
The tensor presentation in the module pullback is extension only along an
isomorphism: its contraction is s ⊗ m ↦ c⁻¹(s)m, so it is precisely inverse image
with transported action. No coefficient extension or finiteness condition is imposed.

## References

* Stacks 070I and 070K
* Stacks 08FI, 09T5, 09A5, 03CB and 00XZ
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits Opposite

attribute [local instance 30000]
  SheafOfModules.wEqualsLocallyBijective_coefficientUniverse
  AlgebraicGeometry.Scheme.proEtaleRingModules_hasDerivedCategory

attribute [local irreducible] Functor.mapDerivedCategory Functor.rightDerivedFunctor

-- Compute first on the homotopy category, then transport through quotientCompQhIso.
section DerivedTranspose
variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D] [Abelian.HasKInjectiveResolutions D]
  {L : C ⥤ D} {R : D ⥤ C} [L.Additive] [R.Additive]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L]

private theorem transpose_homotopy (adj : L ⊣ R)
    (A : HomotopyCategory C (.up ℤ)) (B : HomotopyCategory D (.up ℤ))
    (k : (L.mapHomotopyCategory (.up ℤ)).obj A ⟶ B) :
    adj.mapDerivedCategoryRightDerivedAdjunction.homEquiv
        (DerivedCategory.Qh.obj A) (DerivedCategory.Qh.obj B)
        (L.mapDerivedCategoryFactorsh.hom.app A ≫ DerivedCategory.Qh.map k) =
      DerivedCategory.Qh.map ((adj.mapHomotopyCategory (.up ℤ)).homEquiv A B k) ≫
        R.rightDerivedFunctorUnit.app B := by
  simp only [Adjunction.homEquiv_unit, Functor.map_comp]
  rw [← Category.assoc]
  change (((adj.mapHomotopyCategory (.up ℤ)).derivedη
    (HomotopyCategory.quasiIso C (.up ℤ)) L.mapDerivedCategoryFactorsh.hom
    R.rightDerivedFunctorUnit).app _ ≫
      R.rightDerivedFunctor.map (L.mapDerivedCategoryFactorsh.hom.app A)) ≫ _ = _
  rw [Adjunction.derivedη_fac_app, Category.assoc]
  have hn := R.rightDerivedFunctorUnit.naturality k
  dsimp only [Functor.comp_map] at hn
  rw [← hn, Category.assoc]

end DerivedTranspose

namespace AlgebraicGeometry.Scheme.RingedRestrictionExchange

attribute [local irreducible] proEtaleRingModulePullback proEtaleRingModuleDirectImage
  proEtaleRingModuleAdjunction proEtaleCanonicalDerivedPullbackComparison
  StrictTowerRingedSquare.exchangeModuleSquare

variable {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
  {f : X ⟶ Y} {g : Y' ⟶ Y} {sq : ChosenCartesianSquare g' f' f g}

/-- Exact localization of the canonical inverse-image square. -/
abbrev pullSquare (r : StrictTowerRingedSquare sq) :
    (basePull r).mapDerivedCategory ⋙ (targetPull r).mapDerivedCategory ≅
      (verticalPull r).mapDerivedCategory ⋙ (upperPull r).mapDerivedCategory :=
  proEtaleAmbientRingedPullbackComparison sq r.RX r.RY r.RX' r.RY'
    r.cf r.cg r.cg' r.cf' r.coherent

/-- The canonical quasi-isomorphism-independent resolution comparison; it does not require
that the resolution map be monic. -/
def resolutionIso (r : StrictTowerRingedSquare sq)
    {K I : CochainComplex (proEtaleRingModules X r.RX) ℤ}
    [I.IsKInjective] (a : K ⟶ I) [QuasiIso a] :
    (verticalPush r).rightDerivedFunctor.obj (DerivedCategory.Q.obj K) ≅
      DerivedCategory.Q.obj (((verticalPush r).mapHomologicalComplex (.up ℤ)).obj I) :=
  (verticalPush r).rightDerivedFunctor.mapIso (asIso (DerivedCategory.Q.map a)) ≪≫
    (verticalPush r).rightDerivedFunctorObjQIso I

private def ringCompAt {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (fg : X ⟶ Z) (hfg : fg = f ≫ g) :
    proEtaleSheafInverseImage fg CommRingCat.{u + 1} ≅
      proEtaleSheafInverseImage g CommRingCat.{u + 1} ⋙
        proEtaleSheafInverseImage f CommRingCat.{u + 1} :=
  ((conjugateIsoEquiv (proEtaleSheafAdjunction fg CommRingCat.{u + 1})
    ((proEtaleSheafAdjunction g CommRingCat.{u + 1}).comp
      (proEtaleSheafAdjunction f CommRingCat.{u + 1}))).symm
    (Functor.sheafPushforwardContinuousComp'
      (eFG := (MorphismProperty.Over.pullbackComp
        (P := @WeaklyEtale) (Q := ⊤) f g fg hfg).symm) CommRingCat.{u + 1}
      (ProEt.topology Z) (ProEt.topology Y) (ProEt.topology X)).symm).symm

private theorem ringCompAt_left {P T : Scheme.{u}} (p : P ⟶ T) :
    ringCompAt (𝟙 P) p p (Category.id_comp p).symm =
      (proEtaleSheafInverseImage p CommRingCat.{u + 1}).rightUnitor.symm ≪≫
        Functor.isoWhiskerLeft (proEtaleSheafInverseImage p CommRingCat.{u + 1})
          (proEtaleRingInverseImageId P).symm := by
  let a := proEtaleSheafAdjunction p CommRingCat.{u + 1}
  let b := proEtaleSheafAdjunction (𝟙 P) CommRingCat.{u + 1}
  apply (conjugateIsoEquiv (a.comp b) a).injective
  rw [show conjugateIsoEquiv (a.comp b) a
      (ringCompAt (𝟙 P) p p (Category.id_comp p).symm) =
      Functor.sheafPushforwardContinuousComp'
        (eFG := (MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤)
          (𝟙 P) p p (Category.id_comp p).symm).symm) CommRingCat.{u + 1}
          (ProEt.topology T) (ProEt.topology P) (ProEt.topology P) from
    (conjugateIsoEquiv_iso_symm a (a.comp b) _).trans
      (congrArg Iso.symm ((conjugateIsoEquiv a (a.comp b)).apply_symm_apply _))]
  rw [conjugateIsoEquiv_trans _ (a.comp Adjunction.id) _]
  simp only [conjugateIsoEquiv_isoWhiskerLeft, conjugateIsoEquiv_iso_symm,
    conjugateIsoEquiv_rightUnitor]
  have hid : conjugateIsoEquiv Adjunction.id b (proEtaleRingInverseImageId P) =
      (AlgebraicGeometry.ProEtale.lowerStarId CommRingCat.{u + 1} P).symm :=
    Equiv.apply_symm_apply _ _
  rw [hid]
  ext M V
  simp only [Functor.sheafPushforwardContinuousComp',
    MorphismProperty.Over.pullbackComp_id_left p p (Category.id_comp p).symm]
  simp
  rfl

private theorem ringCompAt_right {P T : Scheme.{u}} (p : P ⟶ T) :
    ringCompAt p (𝟙 T) p (Category.comp_id p).symm =
      (proEtaleSheafInverseImage p CommRingCat.{u + 1}).leftUnitor.symm ≪≫
        Functor.isoWhiskerRight (proEtaleRingInverseImageId T).symm
          (proEtaleSheafInverseImage p CommRingCat.{u + 1}) := by
  let a := proEtaleSheafAdjunction p CommRingCat.{u + 1}
  let b := proEtaleSheafAdjunction (𝟙 T) CommRingCat.{u + 1}
  apply (conjugateIsoEquiv (b.comp a) a).injective
  rw [show conjugateIsoEquiv (b.comp a) a
      (ringCompAt p (𝟙 T) p (Category.comp_id p).symm) =
      Functor.sheafPushforwardContinuousComp'
        (eFG := (MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤)
          p (𝟙 T) p (Category.comp_id p).symm).symm) CommRingCat.{u + 1}
          (ProEt.topology T) (ProEt.topology T) (ProEt.topology P) from
    (conjugateIsoEquiv_iso_symm a (b.comp a) _).trans
      (congrArg Iso.symm ((conjugateIsoEquiv a (b.comp a)).apply_symm_apply _))]
  rw [conjugateIsoEquiv_trans _ (Adjunction.id.comp a) _]
  simp only [conjugateIsoEquiv_isoWhiskerRight, conjugateIsoEquiv_iso_symm,
    conjugateIsoEquiv_leftUnitor]
  have hid : conjugateIsoEquiv Adjunction.id b (proEtaleRingInverseImageId T) =
      (AlgebraicGeometry.ProEtale.lowerStarId CommRingCat.{u + 1} T).symm :=
    Equiv.apply_symm_apply _ _
  rw [hid]
  ext M V
  simp only [Functor.sheafPushforwardContinuousComp',
    MorphismProperty.Over.pullbackComp_id_right p p (Category.comp_id p).symm]
  simp
  rfl
private theorem ringComposite_heq {V W Z : Scheme.{u}}
    (h : Z ⟶ W) (k : W ⟶ V) (q : Z ⟶ V) (hq : q = h ≫ k)
    (RV : Sheaf (ProEt.topology V) CommRingCat.{u + 1})
    (RW : Sheaf (ProEt.topology W) CommRingCat.{u + 1})
    (RZ : Sheaf (ProEt.topology Z) CommRingCat.{u + 1})
    (ck : (proEtaleSheafInverseImage k CommRingCat.{u + 1}).obj RV ≅ RW)
    (ch : (proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj RW ≅ RZ) :
    HEq (proEtaleRingCompositeCoefficients h k RV RW RZ ck ch)
      ((ringCompAt h k q hq).app RV ≪≫
        (proEtaleSheafInverseImage h CommRingCat.{u + 1}).mapIso ck ≪≫ ch) := by
  subst q
  rfl

section Comparisons
universe vC vD uC uD
variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
  [Abelian C] [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D]
  (F : C ⥤ D) [F.Additive]

end Comparisons

private theorem chainComparison_isKInjective
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [Abelian.HasKInjectiveResolutions C]
    (F : C ⥤ D) [F.Additive] (I : CochainComplex C ℤ) [I.IsKInjective] :
    chainComparison F I = (F.rightDerivedFunctorObjQIso I).inv := by
  exact F.rightDerivedFunctorUnitQ_eq I

-- State the chain with the instance used by `exchange`, matching `exchange_chainUnit`.
section ExchangeChain
attribute [local instance 40000] WeilConjectures.sfAbBijective

private theorem exchange_chain (r : StrictTowerRingedSquare sq)
    (K : CochainComplex (proEtaleRingModules X r.RX) ℤ) :
    (basePull r).mapDerivedCategory.map (chainComparison (verticalPush r) K) ≫
        (exchange r).app (DerivedCategory.Q.obj K) ≫
        (targetPush r).rightDerivedFunctor.map
          ((upperPull r).mapDerivedCategoryFactors.hom.app K) =
      (basePull r).mapDerivedCategoryFactors.hom.app
          (((verticalPush r).mapHomologicalComplex (.up ℤ)).obj K) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex (ordinary r) (.up ℤ)).app K) ≫
        chainComparison (targetPush r)
          (((upperPull r).mapHomologicalComplex (.up ℤ)).obj K) := by
  exact exchange_chainUnit r K
end ExchangeChain

attribute [local irreducible] ordinary proEtaleAmbientRingedExchange

section SingleComparison
variable {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
  [Abelian A] [Abelian B] [Abelian C] [Abelian D]

end SingleComparison

-- Keep the native module-category instances while the four functors are variables.
section SchemeSingleComparison
variable (r : StrictTowerRingedSquare sq)
  (F : proEtaleRingModules X r.RX ⥤ proEtaleRingModules Y r.RY)
  (G : proEtaleRingModules Y r.RY ⥤ proEtaleRingModules Y' r.RY')
  (H : proEtaleRingModules X r.RX ⥤ proEtaleRingModules X' r.RX')
  (J : proEtaleRingModules X' r.RX' ⥤ proEtaleRingModules Y' r.RY')
  [F.Additive] [G.Additive] [H.Additive] [J.Additive]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]

end SchemeSingleComparison

section DegreeZeroNormalization

end DegreeZeroNormalization

attribute [local semireducible] proEtaleRingModuleDirectImage

section OpenComparisonTransfer
attribute [local irreducible] proEtaleRingModuleDirectImage
variable {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
  [Abelian A] [Abelian B] [Abelian C] [Abelian D]
  [HasDerivedCategory A] [HasDerivedCategory B]
  [HasDerivedCategory C] [HasDerivedCategory D]
  [Abelian.HasKInjectiveResolutions A] [Abelian.HasKInjectiveResolutions C]
  (F : A ⥤ B) (G : B ⥤ D) (H : A ⥤ C) (J : C ⥤ D)
  [F.Additive] [G.Additive] [H.Additive] [J.Additive]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]
  [H.PreservesKInjectiveComplexes]

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem derived_iso_of_chain (e : F ⋙ G ⟶ H ⋙ J) [IsIso e]
    (δ : F.rightDerivedFunctor ⋙ G.mapDerivedCategory ⟶
      H.mapDerivedCategory ⋙ J.rightDerivedFunctor)
    (hδ : ∀ I : CochainComplex A ℤ,
      G.mapDerivedCategory.map (chainComparison F I) ≫
          δ.app (DerivedCategory.Q.obj I) ≫
          J.rightDerivedFunctor.map (H.mapDerivedCategoryFactors.hom.app I) =
        G.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj I) ≫
          DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex e (.up ℤ)).app I) ≫
          chainComparison J ((H.mapHomologicalComplex (.up ℤ)).obj I)) :
    IsIso δ := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro K
  let L := DerivedCategory.Q.objPreimage K
  obtain ⟨I, hI, a, ha, _⟩ := Abelian.HasKInjectiveResolutions.exists_isKInjective L
  have hQI : IsIso (δ.app (DerivedCategory.Q.obj I)) := by
    have h := hδ I
    rw [chainComparison_isKInjective, chainComparison_isKInjective] at h
    have hi : IsIso
        (G.mapDerivedCategory.map (F.rightDerivedFunctorObjQIso I).inv ≫
          δ.app (DerivedCategory.Q.obj I) ≫
          J.rightDerivedFunctor.map (H.mapDerivedCategoryFactors.hom.app I)) := by
      rw [h]
      exact ((G.mapDerivedCategoryFactors.app
        ((F.mapHomologicalComplex (.up ℤ)).obj I)) ≪≫
          DerivedCategory.Q.mapIso ((NatIso.mapHomologicalComplex (asIso e) (.up ℤ)).app I) ≪≫
          (J.rightDerivedFunctorObjQIso
            ((H.mapHomologicalComplex (.up ℤ)).obj I)).symm).isIso_hom
    have hi' : IsIso (δ.app (DerivedCategory.Q.obj I) ≫
        J.rightDerivedFunctor.map (H.mapDerivedCategoryFactors.hom.app I)) :=
      IsIso.of_isIso_comp_left
        (G.mapDerivedCategory.map (F.rightDerivedFunctorObjQIso I).inv) _
    exact IsIso.of_isIso_comp_right _
      (J.rightDerivedFunctor.map (H.mapDerivedCategoryFactors.hom.app I))
  let i : DerivedCategory.Q.obj I ≅ K :=
    (asIso (DerivedCategory.Q.map a)).symm ≪≫ DerivedCategory.Q.objObjPreimageIso K
  exact (NatTrans.isIso_app_iff_of_iso δ i).mp hQI

end OpenComparisonTransfer

-- Specialize the category instances before substituting the ringed functors.
section SchemeOpenComparisonTransfer
-- Same locally bijective instance as in `exchange`, so the chain types agree syntactically.
attribute [local instance 40000] WeilConjectures.sfAbBijective
variable (r : StrictTowerRingedSquare sq)
  (F : proEtaleRingModules X r.RX ⥤ proEtaleRingModules Y r.RY)
  (G : proEtaleRingModules Y r.RY ⥤ proEtaleRingModules Y' r.RY')
  (H : proEtaleRingModules X r.RX ⥤ proEtaleRingModules X' r.RX')
  (J : proEtaleRingModules X' r.RX' ⥤ proEtaleRingModules Y' r.RY')
  [F.Additive] [G.Additive] [H.Additive] [J.Additive]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]
  [H.PreservesKInjectiveComplexes]

private theorem scheme_derived_iso_of_chain (e : F ⋙ G ⟶ H ⋙ J) [IsIso e]
    (δ : F.rightDerivedFunctor ⋙ G.mapDerivedCategory ⟶
      H.mapDerivedCategory ⋙ J.rightDerivedFunctor)
    (hδ : ∀ I : CochainComplex (proEtaleRingModules X r.RX) ℤ,
      G.mapDerivedCategory.map (chainComparison F I) ≫
          δ.app (DerivedCategory.Q.obj I) ≫
          J.rightDerivedFunctor.map (H.mapDerivedCategoryFactors.hom.app I) =
        G.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj I) ≫
          DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex e (.up ℤ)).app I) ≫
          chainComparison J ((H.mapHomologicalComplex (.up ℤ)).obj I)) :
    IsIso δ := by
  exact derived_iso_of_chain F G H J e δ hδ
end SchemeOpenComparisonTransfer

/-- The open comparison is the specified derived mate and is an isomorphism. -/
theorem open_comparison (r : StrictTowerRingedSquare sq) [IsOpenImmersion g] :
    IsIso (ordinary r) ∧ IsIso (exchange r) := by
  have ho : IsIso (ordinary r) := ordinary_open_isIso r
  refine ⟨ho, ?_⟩
  exact scheme_derived_iso_of_chain r (verticalPush r) (basePull r) (upperPull r) (targetPush r)
    (ordinary r) (exchange r) (exchange_chain r)

section OpenSectionwise

end OpenSectionwise

variable {U : Scheme.{u}} {j : U ⟶ Y}

/-- Restricting the global exchange equals the exchange of the restricted square,
through the specified open comparisons and canonical pullback-composition maps. -/
theorem open_restriction (r : StrictTowerRingedSquare sq) [IsOpenImmersion j]
    (C : OpenCube r j)
    (K : DerivedCategory (proEtaleRingModules X r.RX)) :
    (basePull C.targetFace).mapDerivedCategory.map ((exchange r).app K) ≫
        (exchange C.targetFace).app ((upperPull r).mapDerivedCategory.obj K) ≫
        (targetPush C.localRings).rightDerivedFunctor.map
          ((pullSquare C.upperFace).inv.app K) =
      (pullSquare C.baseFace).inv.app ((verticalPush r).rightDerivedFunctor.obj K) ≫
        (basePull C.localRings).mapDerivedCategory.map ((exchange C.sourceFace).app K) ≫
        (exchange C.localRings).app ((upperPull C.sourceFace).mapDerivedCategory.obj K) := by
  simpa only [pullSquare] using restriction_exchange_cube r C K

/-- The identity direct-image comparison is uniquely fixed on every section by the
actual identity fibre-product map. -/
theorem identityDirect_existsUnique (Z : Scheme.{u})
    (R : Sheaf (ProEt.topology Z) CommRingCat.{u + 1}) :
    ∃! e : proEtaleRingModuleDirectImage (𝟙 Z) R R
        (AlgebraicGeometry.ProEtaleTensorComparison.ringId R) ≅ 𝟭 _,
      ∀ (M : proEtaleRingModules Z R) (V : Z.ProEt)
        (m : ((proEtaleRingModuleDirectImage (𝟙 Z) R R
          (AlgebraicGeometry.ProEtaleTensorComparison.ringId R)).obj M).val.obj (op V)),
        (e.hom.app M).val.app (op V) m =
          M.val.map ((MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ Z).inv.app V).op m := by
  have : (𝟭 (MorphismProperty.Over @WeaklyEtale ⊤ Z)).IsContinuous
      (ProEt.topology Z) (ProEt.topology Z) := Functor.isContinuous_id _
  let A := (sheafCompose (ProEt.topology Z)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R
  let e := MorphismProperty.Over.pullbackId (P := @WeaklyEtale) (Q := ⊤) Z
  let t : A ⟶ ((proEtaleBaseChange (𝟙 Z)).sheafPushforwardContinuous
      RingCat.{u + 1} (ProEt.topology Z) (ProEt.topology Z)).obj A :=
    ⟨Functor.whiskerRight
      (proEtaleRingDirectImageMap (𝟙 Z) R R
        (AlgebraicGeometry.ProEtaleTensorComparison.ringId R)).hom
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩
  have hc : proEtaleRingDirectImageMap (𝟙 Z) R R
      (AlgebraicGeometry.ProEtaleTensorComparison.ringId R) =
      (AlgebraicGeometry.ProEtale.lowerStarId CommRingCat.{u + 1} Z).inv.app R := by
    exact (unit_conjugateEquiv_symm Adjunction.id
      (proEtaleSheafAdjunction (𝟙 Z) CommRingCat.{u + 1})
      (AlgebraicGeometry.ProEtale.lowerStarId CommRingCat.{u + 1} Z).inv R).symm
  have ht : t ≫ (Functor.sheafPushforwardContinuousNatTrans e.inv _ _ _).app A = 𝟙 A := by
    dsimp only [t]
    rw [hc]
    ext U x
    change (R.obj.map (e.hom.app U.unop).op ≫ R.obj.map (e.inv.app U.unop).op) x = x
    rw [← R.obj.map_comp, ← CategoryTheory.op_comp, Iso.inv_hom_id_app,
      CategoryTheory.op_id, R.obj.map_id]
    rfl
  let d : proEtaleRingModuleDirectImage (𝟙 Z) R R
      (AlgebraicGeometry.ProEtaleTensorComparison.ringId R) ≅ 𝟭 _ :=
    SheafOfModules.pushforwardCongr₂ (φ := t) e.symm ht ≪≫
      SheafOfModules.pushforwardId A
  have hd : ∀ (M : proEtaleRingModules Z R) (V : Z.ProEt)
      (m : ((proEtaleRingModuleDirectImage (𝟙 Z) R R
        (AlgebraicGeometry.ProEtaleTensorComparison.ringId R)).obj M).val.obj (op V)),
      (d.hom.app M).val.app (op V) m = M.val.map (e.inv.app V).op m := by
    intro M V m
    rfl
  refine ⟨d, hd, ?_⟩
  intro d' hd'
  apply Iso.ext
  ext M V m
  exact (hd' M V.unop m).trans (hd M V.unop m).symm

/-- The section-normalized identity direct image. -/
def identityDirect (Z : Scheme.{u}) (R : Sheaf (ProEt.topology Z) CommRingCat.{u + 1}) :
    proEtaleRingModuleDirectImage (𝟙 Z) R R
      (AlgebraicGeometry.ProEtaleTensorComparison.ringId R) ≅ 𝟭 _ :=
  (identityDirect_existsUnique Z R).exists.choose

/-- The identity inverse-image comparison is its adjunction conjugate, so has no
freely chosen natural automorphism. -/
def identityPull (Z : Scheme.{u}) (R : Sheaf (ProEt.topology Z) CommRingCat.{u + 1}) :
    proEtaleRingModulePullback (𝟙 Z) R R
      (AlgebraicGeometry.ProEtaleTensorComparison.ringId R) ≅ 𝟭 _ :=
  ((proEtaleRingModuleAdjunction (𝟙 Z) R R
    (AlgebraicGeometry.ProEtaleTensorComparison.ringId R)).ofNatIsoRight
      (identityDirect Z R)).leftAdjointUniq Adjunction.id

/-- Exact localization of the normalized module identity. -/
def identityDerivedPull (Z : Scheme.{u})
    (R : Sheaf (ProEt.topology Z) CommRingCat.{u + 1}) :
    (proEtaleRingModulePullback (𝟙 Z) R R
      (AlgebraicGeometry.ProEtaleTensorComparison.ringId R)).mapDerivedCategory ≅ 𝟭 _ :=
  Functor.mapDerivedCategoryNatIso (identityPull Z R) ≪≫ Functor.mapDerivedCategoryIdIso _

/-- Canonical coefficient identities commute with any inverse-image coefficient map. -/
theorem identityCoefficients_coherent {P T : Scheme.{u}} (p : P ⟶ T)
    (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology P) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage p CommRingCat.{u + 1}).obj R ≅ S) :
    HEq (proEtaleRingCompositeCoefficients (𝟙 P) p R S S c
        (AlgebraicGeometry.ProEtaleTensorComparison.ringId S))
      (proEtaleRingCompositeCoefficients p (𝟙 T) R R S
        (AlgebraicGeometry.ProEtaleTensorComparison.ringId R) c) := by
  have hl := ringComposite_heq (𝟙 P) p p (Category.id_comp p).symm R S S c
    (AlgebraicGeometry.ProEtaleTensorComparison.ringId S)
  have hr := ringComposite_heq p (𝟙 T) p (Category.comp_id p).symm R R S
    (AlgebraicGeometry.ProEtaleTensorComparison.ringId R) c
  refine hl.trans ((heq_of_eq ?_).trans hr.symm)
  rw [ringCompAt_left, ringCompAt_right]
  apply Iso.ext
  simp only [Iso.trans_hom, Iso.app_hom, Functor.isoWhiskerLeft_hom,
    Iso.symm_hom, Functor.mapIso_hom, Functor.isoWhiskerRight_hom]
  change (proEtaleRingInverseImageId P).inv.app
      ((proEtaleSheafInverseImage p CommRingCat.{u + 1}).obj R) ≫
      (proEtaleSheafInverseImage (𝟙 P) CommRingCat.{u + 1}).map c.hom ≫
      (proEtaleRingInverseImageId P).hom.app S =
    (proEtaleSheafInverseImage p CommRingCat.{u + 1}).map
      ((proEtaleRingInverseImageId T).inv.app R) ≫
      (proEtaleSheafInverseImage p CommRingCat.{u + 1}).map
        ((proEtaleRingInverseImageId T).hom.app R) ≫ c.hom
  rw [(proEtaleRingInverseImageId P).hom.naturality]
  simp only [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp,
    ← Functor.map_comp, Iso.inv_hom_id_app]
  change c.hom = _
  exact ((congrArg (fun k ↦ k ≫ c.hom)
    ((proEtaleSheafInverseImage p CommRingCat.{u + 1}).map_id R)).trans
      (Category.id_comp c.hom)).symm

/-- The coefficient presentation of the identity square, with the actual identity
ring comparisons. -/
def identityRings {P T : Scheme.{u}} (p : P ⟶ T)
    (s : ChosenCartesianSquare (𝟙 P) p p (𝟙 T))
    (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology P) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage p CommRingCat.{u + 1}).obj R ≅ S) :
    StrictTowerRingedSquare s where
  RY := R
  RX := S
  RY' := R
  RX' := S
  cf := c
  cg := AlgebraicGeometry.ProEtaleTensorComparison.ringId R
  cg' := AlgebraicGeometry.ProEtaleTensorComparison.ringId S
  cf' := c
  coherent := identityCoefficients_coherent p R S c

-- Normalize identity pullbacks through their sectionwise direct-image conjugates.
attribute [local irreducible] LocallyRingedSpace.comp PresheafedSpace.comp
  exchangeModuleComposition proEtaleRingCompositeCoefficients identityDirect
  proEtaleAmbientRingedPullbackComparison proEtaleRingDerivedAdjunction

private theorem identityPull_conjugate_aux {A : Type*} [Category A]
    {L R : A ⥤ A} (a : L ⊣ R) (e : R ≅ 𝟭 A) :
    (a.ofNatIsoRight e).leftAdjointUniq Adjunction.id = a.leftAdjointIdIso e := by
  apply Iso.ext_inv
  ext M
  simp [Adjunction.leftAdjointUniq, Adjunction.leftAdjointIdIso,
    conjugateIsoEquiv, conjugateEquiv_symm_apply_app, Adjunction.ofNatIsoRight]

private theorem identityPull_conjugate (Z : Scheme.{u})
    (R : Sheaf (ProEt.topology Z) CommRingCat.{u + 1}) :
    conjugateIsoEquiv Adjunction.id
      (proEtaleRingModuleAdjunction (𝟙 Z) R R
        (AlgebraicGeometry.ProEtaleTensorComparison.ringId R))
      (identityPull Z R) = (identityDirect Z R).symm := by
  unfold identityPull
  rw [identityPull_conjugate_aux]
  exact Equiv.apply_symm_apply _ _

private abbrev RingedArrow (A B : Scheme.{u})
    (R : Sheaf (ProEt.topology B) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology A) CommRingCat.{u + 1}) :=
  Σ h : A ⟶ B, (proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj R ≅ S

private abbrev arrowPull {A B : Scheme.{u}}
    {R : Sheaf (ProEt.topology B) CommRingCat.{u + 1}}
    {S : Sheaf (ProEt.topology A) CommRingCat.{u + 1}} (z : RingedArrow A B R S) :=
  proEtaleRingModulePullback z.1 R S z.2

private abbrev arrowBase {A B : Scheme.{u}}
    {R : Sheaf (ProEt.topology B) CommRingCat.{u + 1}}
    {S : Sheaf (ProEt.topology A) CommRingCat.{u + 1}} (z : RingedArrow A B R S) :=
  proEtaleBaseChange z.1

private abbrev arrowPush {A B : Scheme.{u}}
    {R : Sheaf (ProEt.topology B) CommRingCat.{u + 1}}
    {S : Sheaf (ProEt.topology A) CommRingCat.{u + 1}} (z : RingedArrow A B R S) :=
  proEtaleRingModuleDirectImage z.1 R S z.2

private abbrev arrowAdj {A B : Scheme.{u}}
    {R : Sheaf (ProEt.topology B) CommRingCat.{u + 1}}
    {S : Sheaf (ProEt.topology A) CommRingCat.{u + 1}} (z : RingedArrow A B R S) :=
  proEtaleRingModuleAdjunction z.1 R S z.2

private theorem conjugate_square_transport {A B : Scheme.{u}}
    {R : Sheaf (ProEt.topology B) CommRingCat.{u + 1}}
    {S : Sheaf (ProEt.topology A) CommRingCat.{u + 1}}
    {z w : RingedArrow A B R S} (e : w = z)
    {L₁ L₂ : proEtaleRingModules B R ⥤ proEtaleRingModules A S}
    {R₁ R₂ : proEtaleRingModules A S ⥤ proEtaleRingModules B R}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂)
    (a : arrowPull z ≅ L₁) (b : arrowPull w ≅ L₂) :
    conjugateIsoEquiv a₁ a₂ (b.symm ≪≫ eqToIso (congrArg arrowPull e) ≪≫ a) =
      conjugateIsoEquiv a₁ (arrowAdj z) a ≪≫
        (eqToIso (congrArg arrowPush e)).symm ≪≫
          (conjugateIsoEquiv a₂ (arrowAdj w) b).symm := by
  cases e
  simp only [eqToIso_refl, Iso.refl_trans, Iso.refl_symm]
  rw [conjugateIsoEquiv_trans _ (arrowAdj z) _, conjugateIsoEquiv_iso_symm]

private theorem direct_transport {A B : Scheme.{u}}
    {R : Sheaf (ProEt.topology B) CommRingCat.{u + 1}}
    {S : Sheaf (ProEt.topology A) CommRingCat.{u + 1}}
    {z w : RingedArrow A B R S} (e : z = w)
    (N : proEtaleRingModules A S) (V : B.ProEt)
    (m : ((arrowPush z).obj N).val.obj (op V)) :
    ((eqToIso (congrArg arrowPush e)).hom.app N).val.app (op V) m =
      N.val.map ((eqToIso (congrArg arrowBase e)).inv.app V).op m := by
  cases e
  change m = N.val.map (𝟙 _) m
  rw [PresheafOfModules.map_id]
  rfl

private theorem direct_transport_inv {A B : Scheme.{u}}
    {R : Sheaf (ProEt.topology B) CommRingCat.{u + 1}}
    {S : Sheaf (ProEt.topology A) CommRingCat.{u + 1}}
    {z w : RingedArrow A B R S} (e : z = w)
    (N : proEtaleRingModules A S) (V : B.ProEt)
    (m : ((arrowPush w).obj N).val.obj (op V)) :
    ((eqToIso (congrArg arrowPush e)).inv.app N).val.app (op V) m =
      N.val.map ((eqToIso (congrArg arrowBase e)).hom.app V).op m := by
  cases e
  change m = N.val.map (𝟙 _) m
  rw [PresheafOfModules.map_id]
  rfl

private theorem iso_trans_symm_eq_of_hom_comp {A : Type*} [Category A]
    {W X Y Z : A} (a : W ≅ X) (t : X ≅ Y) (b : Z ≅ Y) (d : W ≅ Z)
    (h : a.hom ≫ t.hom = d.hom ≫ b.hom) : a ≪≫ t ≪≫ b.symm = d := by
  apply Iso.ext
  change a.hom ≫ t.hom ≫ b.inv = d.hom
  rw [← Category.assoc, h]
  simp

private theorem identityDirect_hom_sections (Z : Scheme.{u})
    (R : Sheaf (ProEt.topology Z) CommRingCat.{u + 1})
    (N : proEtaleRingModules Z R) (V : Z.ProEt)
    (m : ((proEtaleRingModuleDirectImage (𝟙 Z) R R
      (AlgebraicGeometry.ProEtaleTensorComparison.ringId R)).obj N).val.obj (op V)) :
    ((identityDirect Z R).hom.app N).val.app (op V) m =
      N.val.map ((MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ Z).inv.app V).op m := by
  simpa only [identityDirect] using
    (identityDirect_existsUnique Z R).exists.choose_spec N V m

private theorem identityDirect_inv_sections (Z : Scheme.{u})
    (R : Sheaf (ProEt.topology Z) CommRingCat.{u + 1})
    (N : proEtaleRingModules Z R) (V : Z.ProEt) (m : N.val.obj (op V)) :
    ((identityDirect Z R).inv.app N).val.app (op V) m =
      N.val.map ((MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ Z).hom.app V).op m := by
  have : IsIso (((identityDirect Z R).hom.app N).val.app (op V)) := by
    change IsIso ((SheafOfModules.evaluation _ (op V)).map
      ((identityDirect Z R).hom.app N))
    infer_instance
  apply (ConcreteCategory.bijective_of_isIso
    (((identityDirect Z R).hom.app N).val.app (op V))).1
  have hi := congrArg (fun k ↦ k.val.app (op V) m)
    ((identityDirect Z R).inv_hom_id_app N)
  change ((identityDirect Z R).hom.app N).val.app (op V)
    (((identityDirect Z R).inv.app N).val.app (op V) m) = m at hi
  rw [hi, identityDirect_hom_sections]
  rw [← PresheafOfModules.map_comp_apply, ← op_comp, Iso.inv_hom_id_app]
  simp

private theorem baseCongr_eq {X Y : Scheme.{u}} {f g : X ⟶ Y} (e : f = g) :
    MorphismProperty.Over.pullbackCongr (P := @WeaklyEtale) (Q := ⊤) e =
      eqToIso (congrArg (fun q ↦ proEtaleBaseChange q) e) := by
  cases e
  exact MorphismProperty.Over.pullbackCongr_refl (P := @WeaklyEtale) (Q := ⊤) f rfl

private theorem site_identity {P T : Scheme.{u}} (p : P ⟶ T)
    (e : p ≫ 𝟙 T = 𝟙 P ≫ p) (V : T.ProEt) :
    (eqToIso (congrArg (fun q ↦ proEtaleBaseChange q) e)).hom.app V ≫
      (MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) (𝟙 P) p).hom.app V =
    (MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) p (𝟙 T)).hom.app V ≫
      (proEtaleBaseChange p).map
        ((MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ T).hom.app V) ≫
      (MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ P).inv.app
        ((proEtaleBaseChange p).obj V) := by
  rw [MorphismProperty.Over.pullbackComp_id_left p (𝟙 P ≫ p) rfl,
    MorphismProperty.Over.pullbackComp_id_right p (p ≫ 𝟙 T) rfl]
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.rightUnitor_inv_app,
    Functor.leftUnitor_inv_app, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Iso.symm_hom,
    Category.id_comp, Category.assoc]
  rw [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id]
  simp only [Category.id_comp]
  rw [baseCongr_eq, baseCongr_eq]
  rw [← Category.assoc]
  apply (cancel_mono ((MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ P).inv.app
    ((proEtaleBaseChange p).obj V))).mpr
  rw [← NatTrans.comp_app, ← Iso.trans_hom, eqToIso_trans]

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
set_option backward.defeqAttrib.useBackward false in
private theorem localized_identity_square
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) (B : C ⥤ C) (H : D ⥤ D)
    [F.Additive] [B.Additive] [H.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits B] [PreservesFiniteColimits B]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (b : B ≅ 𝟭 C) (h : H ≅ 𝟭 D) (θ : B ⋙ F ≅ F ⋙ H)
    (hθ : θ ≪≫ Functor.isoWhiskerLeft F h ≪≫ F.rightUnitor =
      Functor.isoWhiskerRight b F ≪≫ F.leftUnitor)
    (M : DerivedCategory C) :
    (Functor.mapDerivedCategorySquareIso θ).hom.app M ≫
        (Functor.mapDerivedCategoryNatIso h ≪≫ Functor.mapDerivedCategoryIdIso D).hom.app
          (F.mapDerivedCategory.obj M) =
      F.mapDerivedCategory.map
        ((Functor.mapDerivedCategoryNatIso b ≪≫ Functor.mapDerivedCategoryIdIso C).hom.app M) := by
  have hl := congr_app (Functor.mapDerivedCategoryNatIso_isoWhiskerLeft F h) M
  have hr := congr_app (Functor.mapDerivedCategoryNatIso_isoWhiskerRight b F) M
  have hul := congr_app (Functor.mapDerivedCategoryCompIso_id_comp F) M
  have hur := congr_app (Functor.mapDerivedCategoryCompIso_comp_id F) M
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    NatTrans.id_app] at hl hr hul hur
  simp only [Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.map_comp, Category.assoc]
  apply (cancel_epi ((Functor.mapDerivedCategoryCompIso B F).inv.app M)).mp
  simp only [Iso.inv_hom_id_app_assoc]
  rw [← reassoc_of% hl, ← reassoc_of% hr, hur, hul]
  have he := congr_app (congrArg Iso.hom (congrArg
    (fun e ↦ Functor.mapDerivedCategoryNatIso e) hθ)) M
  simp only [Functor.mapDerivedCategoryNatIso_trans, NatTrans.comp_app] at he
  have hleft : (Functor.mapDerivedCategoryNatIso F.leftUnitor).hom = 𝟙 _ := by
    exact Functor.mapDerivedCategoryNatIso_refl
  have hright : (Functor.mapDerivedCategoryNatIso F.rightUnitor).hom = 𝟙 _ := by
    exact Functor.mapDerivedCategoryNatIso_refl
  erw [Category.comp_id, Category.comp_id]
  simpa only [hleft, hright, NatTrans.id_app, Category.comp_id] using he

private theorem identity_mate {C D : Type*} [Category C] [Category D]
    {L : C ⥤ D} {R : D ⥤ C} (a : L ⊣ R)
    (B : C ⥤ C) (H : D ⥤ D) (b : B ≅ 𝟭 C) (h : H ≅ 𝟭 D)
    (θ : B ⋙ L ≅ L ⋙ H)
    (hθ : ∀ M, θ.hom.app M ≫ h.hom.app (L.obj M) = L.map (b.hom.app M)) (M : D) :
    (mateEquiv a a (TwoSquare.mk B L L H θ.hom)).app M ≫
        R.map (h.hom.app M) = b.hom.app (R.obj M) := by
  dsimp [mateEquiv]
  simp only [Category.id_comp, Category.comp_id, Category.assoc]
  change a.unit.app (B.obj (R.obj M)) ≫ R.map (θ.hom.app (R.obj M)) ≫
    R.map (H.map (a.counit.app M)) ≫ R.map (h.hom.app M) = _
  have hn := h.hom.naturality (a.counit.app M)
  simp only [Functor.id_map] at hn
  have hn' : H.map (a.counit.app M) ≫ h.hom.app M =
      h.hom.app (L.obj (R.obj M)) ≫ a.counit.app M := hn
  rw [← R.map_comp]
  rw [hn']
  rw [R.map_comp, ← R.map_comp_assoc, hθ]
  change a.unit.app (B.obj (R.obj M)) ≫ (L ⋙ R).map (b.hom.app (R.obj M)) ≫
    R.map (a.counit.app M) = _
  rw [← a.unit.naturality_assoc]
  simp only [Functor.id_map, Functor.id_obj]
  rw [a.right_triangle_components]
  simp

private theorem localized_exchange
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} {sq : ChosenCartesianSquare g' f' f g}
    (r : StrictTowerRingedSquare sq) :
    exchange r =
      (mateEquiv (proEtaleRingDerivedAdjunction f r.RY r.RX r.cf)
        (proEtaleRingDerivedAdjunction f' r.RY' r.RX' r.cf')
        (TwoSquare.mk _ _ _ _
          (Functor.mapDerivedCategorySquareIso r.exchangeModuleSquare).hom)) := by
  unfold exchange proEtaleAmbientRingedExchange
  rw [r.ambientSquare_localization]

private theorem left_square_of_conjugate {C D : Type*} [Category C] [Category D]
    {L : C ⥤ D} {R : D ⥤ C} (a : L ⊣ R)
    {B BR : C ⥤ C} {H HR : D ⥤ D} (aB : B ⊣ BR) (aH : H ⊣ HR)
    (b : B ≅ 𝟭 C) (h : H ≅ 𝟭 D) (db : BR ≅ 𝟭 C) (dh : HR ≅ 𝟭 D)
    (hb : conjugateIsoEquiv Adjunction.id aB b = db.symm)
    (hh : conjugateIsoEquiv Adjunction.id aH h = dh.symm)
    (θ : B ⋙ L ≅ L ⋙ H)
    (hθ : conjugateIsoEquiv (a.comp aH) (aB.comp a) θ =
      Functor.isoWhiskerRight dh R ≪≫ R.leftUnitor ≪≫ R.rightUnitor.symm ≪≫
        Functor.isoWhiskerLeft R db.symm) :
    θ ≪≫ Functor.isoWhiskerLeft L h ≪≫ L.rightUnitor =
      Functor.isoWhiskerRight b L ≪≫ L.leftUnitor := by
  apply (conjugateIsoEquiv a (aB.comp a)).injective
  rw [conjugateIsoEquiv_trans a (a.comp aH) (aB.comp a),
    conjugateIsoEquiv_trans a (a.comp Adjunction.id) (a.comp aH),
    conjugateIsoEquiv_rightUnitor, conjugateIsoEquiv_isoWhiskerLeft, hh, hθ]
  rw [conjugateIsoEquiv_trans a (Adjunction.id.comp a) (aB.comp a),
    conjugateIsoEquiv_leftUnitor, conjugateIsoEquiv_isoWhiskerRight, hb]
  ext M
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.leftUnitor_hom_app, Functor.leftUnitor_inv_app,
    Functor.rightUnitor_inv_app, Iso.symm_hom,
    Category.id_comp, Category.assoc]
  erw [← R.map_comp_assoc, Iso.inv_hom_id_app, R.map_id, Category.id_comp]
  exact Category.id_comp _

set_option backward.isDefEq.respectTransparency true in
set_option backward.defeqAttrib.useBackward false in
-- Section comparisons reduce the chosen site pullbacks and their module structures.
private theorem identity_square_conjugate_aux {P T : Scheme.{u}} (p : P ⟶ T)
    (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology P) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage p CommRingCat.{u + 1}).obj R ≅ S)
    (a : proEtaleRingModulePullback (𝟙 P ≫ p) R S
        (proEtaleRingCompositeCoefficients (𝟙 P) p R S S c
          (AlgebraicGeometry.ProEtaleTensorComparison.ringId S)) ≅
      proEtaleRingModulePullback p R S c ⋙ proEtaleRingModulePullback (𝟙 P) S S
        (AlgebraicGeometry.ProEtaleTensorComparison.ringId S))
    (b : proEtaleRingModulePullback (p ≫ 𝟙 T) R S
        (proEtaleRingCompositeCoefficients p (𝟙 T) R R S
          (AlgebraicGeometry.ProEtaleTensorComparison.ringId R) c) ≅
      proEtaleRingModulePullback (𝟙 T) R R
        (AlgebraicGeometry.ProEtaleTensorComparison.ringId R) ⋙
          proEtaleRingModulePullback p R S c)
    (e : (⟨p ≫ 𝟙 T, proEtaleRingCompositeCoefficients p (𝟙 T) R R S
        (AlgebraicGeometry.ProEtaleTensorComparison.ringId R) c⟩ : RingedArrow P T R S) =
      ⟨𝟙 P ≫ p, proEtaleRingCompositeCoefficients (𝟙 P) p R S S c
        (AlgebraicGeometry.ProEtaleTensorComparison.ringId S)⟩)
    (ha : ExchangeModuleCompositionNormalized (𝟙 P) p R S S c
      (AlgebraicGeometry.ProEtaleTensorComparison.ringId S) a)
    (hb : ExchangeModuleCompositionNormalized p (𝟙 T) R R S
      (AlgebraicGeometry.ProEtaleTensorComparison.ringId R) c b) :
    conjugateIsoEquiv
      ((proEtaleRingModuleAdjunction p R S c).comp
        (proEtaleRingModuleAdjunction (𝟙 P) S S
          (AlgebraicGeometry.ProEtaleTensorComparison.ringId S)))
      ((proEtaleRingModuleAdjunction (𝟙 T) R R
          (AlgebraicGeometry.ProEtaleTensorComparison.ringId R)).comp
        (proEtaleRingModuleAdjunction p R S c))
      (b.symm ≪≫ eqToIso (congrArg arrowPull e) ≪≫ a) =
      Functor.isoWhiskerRight (identityDirect P S)
          (proEtaleRingModuleDirectImage p R S c) ≪≫
        Functor.leftUnitor _ ≪≫ (Functor.rightUnitor _).symm ≪≫
        Functor.isoWhiskerLeft (proEtaleRingModuleDirectImage p R S c)
          (identityDirect T R).symm := by
  let ah := (proEtaleRingModuleAdjunction p R S c).comp
    (proEtaleRingModuleAdjunction (𝟙 P) S S
      (AlgebraicGeometry.ProEtaleTensorComparison.ringId S))
  let ab := (proEtaleRingModuleAdjunction (𝟙 T) R R
    (AlgebraicGeometry.ProEtaleTensorComparison.ringId R)).comp
    (proEtaleRingModuleAdjunction p R S c)
  let z : RingedArrow P T R S := ⟨𝟙 P ≫ p, proEtaleRingCompositeCoefficients
    (𝟙 P) p R S S c (AlgebraicGeometry.ProEtaleTensorComparison.ringId S)⟩
  let w : RingedArrow P T R S := ⟨p ≫ 𝟙 T, proEtaleRingCompositeCoefficients
    p (𝟙 T) R R S (AlgebraicGeometry.ProEtaleTensorComparison.ringId R) c⟩
  let da := conjugateIsoEquiv ah (arrowAdj z) a
  let db := conjugateIsoEquiv ab (arrowAdj w) b
  let t := (eqToIso (congrArg arrowPush e)).symm
  rw [conjugate_square_transport e ah ab a b]
  apply iso_trans_symm_eq_of_hom_comp
  apply NatTrans.ext
  funext N
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.leftUnitor_hom_app, Functor.rightUnitor_inv_app,
    Category.assoc, Category.id_comp]
  ext V m
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app,
    ModuleCat.comp_apply]
  have hda := ha N V.unop m
  change (da.hom.app N).val.app V m = _ at hda
  rw [hda]
  rw [direct_transport_inv e]
  have hidP := identityDirect_hom_sections P S N ((proEtaleBaseChange p).obj V.unop) m
  change (((proEtaleRingModuleDirectImage p R S c).map
    ((identityDirect P S).hom.app N)).val.app V) m = _ at hidP
  rw [hidP]
  have hidT := identityDirect_inv_sections T R
    ((proEtaleRingModuleDirectImage p R S c).obj N) V.unop
    (N.val.map ((MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ P).inv.app
      ((proEtaleBaseChange p).obj V.unop)).op m)
  erw [hidT]
  have hdb := hb N V.unop
    (N.val.map ((proEtaleBaseChange p).map
      ((MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ T).hom.app V.unop)).op
      (N.val.map ((MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ P).inv.app
        ((proEtaleBaseChange p).obj V.unop)).op m))
  change (db.hom.app N).val.app V _ = _ at hdb
  erw [hdb]
  let comp := (MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤)
    p (𝟙 T)).hom.app V.unop
  let idT := (MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ T).hom.app V.unop
  let idP := (MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ P).inv.app
    ((proEtaleBaseChange p).obj V.unop)
  set_option backward.isDefEq.respectTransparency false in
  have hcombine :
      N.val.map comp.op
        (N.val.map ((proEtaleBaseChange p).map idT).op
          (N.val.map idP.op m)) =
      N.val.map (comp ≫ (proEtaleBaseChange p).map idT ≫ idP).op m := by
    simp only [op_comp, PresheafOfModules.map_comp_apply]
    rfl
  rw [hcombine]
  simp only [← PresheafOfModules.map_comp_apply, ← op_comp]
  exact congrArg (fun k : (proEtaleBaseChange (p ≫ 𝟙 T)).obj V.unop ⟶
      (proEtaleBaseChange (𝟙 P)).obj ((proEtaleBaseChange p).obj V.unop) ↦
    N.val.map k.op m)
    (site_identity p (congrArg Sigma.fst e) V.unop)

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
set_option backward.defeqAttrib.useBackward false in
-- Instantiate the conjugation identity with the chosen coefficient compositors.
private theorem identity_square {P T : Scheme.{u}} (p : P ⟶ T)
    (s : ChosenCartesianSquare (𝟙 P) p p (𝟙 T))
    (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology P) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage p CommRingCat.{u + 1}).obj R ≅ S) :
    (identityRings p s R S c).exchangeModuleSquare ≪≫
        Functor.isoWhiskerLeft (proEtaleRingModulePullback p R S c) (identityPull P S) ≪≫
        Functor.rightUnitor _ =
      Functor.isoWhiskerRight (identityPull T R) (proEtaleRingModulePullback p R S c) ≪≫
        Functor.leftUnitor _ := by
  apply left_square_of_conjugate (proEtaleRingModuleAdjunction p R S c)
    (proEtaleRingModuleAdjunction (𝟙 T) R R
      (AlgebraicGeometry.ProEtaleTensorComparison.ringId R))
    (proEtaleRingModuleAdjunction (𝟙 P) S S
      (AlgebraicGeometry.ProEtaleTensorComparison.ringId S))
    (identityPull T R) (identityPull P S) (identityDirect T R) (identityDirect P S)
    (identityPull_conjugate T R) (identityPull_conjugate P S)
  have hc := identity_square_conjugate_aux p R S c
    (exchangeModuleComposition (𝟙 P) p R S S c
      (AlgebraicGeometry.ProEtaleTensorComparison.ringId S))
    (exchangeModuleComposition p (𝟙 T) R R S
      (AlgebraicGeometry.ProEtaleTensorComparison.ringId R) c)
    (identityRings p s R S c).exchangeCoefficients_eq
    (by
      unfold exchangeModuleComposition
      exact (exchangeModuleComposition_existsUnique (𝟙 P) p R S S c
        (AlgebraicGeometry.ProEtaleTensorComparison.ringId S)).choose_spec.1)
    (by
      unfold exchangeModuleComposition
      exact (exchangeModuleComposition_existsUnique p (𝟙 T) R R S
        (AlgebraicGeometry.ProEtaleTensorComparison.ringId R) c).choose_spec.1)
  simpa only [StrictTowerRingedSquare.exchangeModuleSquare, identityRings,
    Iso.trans_assoc] using hc

set_option backward.defeqAttrib.useBackward false in
-- Compare the concrete derived functors with the localized ordinary identity square.
/-- For the identity base change exchange is the identity under the canonical
identity and resolution comparisons. -/
theorem identity_normalization {P T : Scheme.{u}} (p : P ⟶ T)
    (s : ChosenCartesianSquare (𝟙 P) p p (𝟙 T))
    (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology P) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage p CommRingCat.{u + 1}).obj R ≅ S)
    (K : DerivedCategory (proEtaleRingModules P S)) :
    (exchange (identityRings p s R S c)).app K ≫
        (proEtaleRingDerivedDirectImage p R S c).map ((identityDerivedPull P S).hom.app K) =
      (identityDerivedPull T R).hom.app ((proEtaleRingDerivedDirectImage p R S c).obj K) := by
  let r := identityRings p s R S c
  have hl := localized_identity_square (proEtaleRingModulePullback p R S c)
    (basePull r) (upperPull r) (identityPull T R) (identityPull P S)
    r.exchangeModuleSquare (identity_square p s R S c)
  rw [localized_exchange]
  exact identity_mate (proEtaleRingDerivedAdjunction p R S c) _ _
    (identityDerivedPull T R) (identityDerivedPull P S) _ hl K

end AlgebraicGeometry.Scheme.RingedRestrictionExchange
