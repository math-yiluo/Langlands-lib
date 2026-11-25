/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientScalars
public import WeilConjectures.AlgebraicGeometry.Canonical.CanonicalDiagonalRightDerived
public import WeilConjectures.AlgebraicGeometry.IntegralFiniteScalar.IntegralFiniteScalarModelDefinitions
import WeilConjectures.AlgebraicGeometry.IntegralFiniteScalar.FiniteFreeScalarDerivedComparison
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixDerivedPullbackNormalization
import WeilConjectures.Mathlib.CategoryTheory.Functor.Derived.Adjunction
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.AlgebraicGeometry.ComapUpperStarIsoMate
import all WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafChangeAdjunctionSupplement

/-! # Finite point resolutions and normalized scalar squares -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
universe u a v w wc
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

private instance scalarRingComm (Λ : CondensedRing.ScalarSixRing.{u}) :
    IsCommMonObj Λ.X := Λ.comm

private instance scalarMapMon {Λ Λ' : CondensedRing.ScalarSixRing.{u}} (a : Λ ⟶ Λ') :
    IsMonHom a.hom.hom := a.hom.isMonHom_hom

attribute [local irreducible] DerivedCategory HasDerivedCategory.ofIsGrothendieckAbelian
  HasDerivedCategory.ofHasKInjectiveResolutions
attribute [local irreducible] upperStarFromPoint Functor.rightDerivedFunctor
  Functor.mapDerivedCategory Functor.leftDerivedFunctor

private theorem canonicalDerives
    {A B : Type a} [Category.{v} A] [Category.{v} B]
    [Abelian A] [Abelian B] [HasDerivedCategory.{wc} B]
    (F : A ⥤ B) [F.Additive] :
    (CochainComplex.KInjectives.localizerMorphism A).Derives
      (F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q) := by
  intro I J f hf
  have : I.obj.IsKInjective := I.property
  have : J.obj.IsKInjective := J.property
  have : QuasiIso f.hom := hf
  obtain ⟨e, he⟩ := (CochainComplex.IsKInjective.quasiIso_iff f.hom).mp
    (inferInstance : QuasiIso f.hom)
  have : QuasiIso ((F.mapHomologicalComplex (.up ℤ)).map f.hom) := by
    rw [← he]
    exact (F.mapHomotopyEquiv e).quasiIso_hom
  change IsIso (DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map f.hom))
  infer_instance

private theorem square_unique
    {A B C D : Type a} [Category.{v} A] [Category.{v} B]
    [Category.{v} C] [Category.{v} D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
    [HasDerivedCategory.{wc} C] [HasDerivedCategory.{wc} D]
    [Abelian.HasKInjectiveResolutions A]
    (F : A ⥤ B) (G : C ⥤ D) [F.Additive] [G.Additive]
    (U : A ⥤ C) (V : B ⥤ D) [U.Additive] [V.Additive]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    (RF : DiagonalRightDerived F) (RG : DiagonalRightDerived G)
    (e : F ⋙ V ≅ U ⋙ G)
    (s t : DiagonalTrace.ExactSquareOfUniverses F G U V RF RG e) : s.iso = t.iso := by
  let eta : (F ⋙ V).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ (RF.R ⋙ V.mapDerivedCategory) :=
    Functor.whiskerLeft (F.mapHomologicalComplex (.up ℤ))
      V.mapDerivedCategoryFactors.inv ≫ Functor.whiskerRight RF.η V.mapDerivedCategory
  have : (RF.R ⋙ V.mapDerivedCategory).IsRightDerivedFunctor eta
      (HomologicalComplex.quasiIso A (.up ℤ)) := by
    apply (canonicalDerives (F ⋙ V)).isRightDerivedFunctor_of_isIso eta
    intro I
    have := RF.computation I.obj I.property
    change IsIso (V.mapDerivedCategoryFactors.inv.app
      ((F.mapHomologicalComplex (.up ℤ)).obj I.obj) ≫
      V.mapDerivedCategory.map (RF.η.app I.obj))
    infer_instance
  apply Iso.ext
  apply Functor.rightDerived_ext _ eta (HomologicalComplex.quasiIso A (.up ℤ))
  ext P
  have hs := s.normalization P
  have ht := t.normalization P
  have hh := hs.trans ht.symm
  rw [← Category.assoc, ← Category.assoc, cancel_mono] at hh
  simp only [eta, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Category.assoc]
  exact congrArg (fun k ↦ V.mapDerivedCategoryFactors.inv.app _ ≫ k) hh

private theorem push_conjugate
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {TX : A ⥤ B} {UX : B ⥤ A} {TY : C ⥤ D} {UY : D ⥤ C}
    {LX : C ⥤ A} {RX : A ⥤ C} {LY : D ⥤ B} {RY : B ⥤ D}
    (ax : TX ⊣ UX) (ay : TY ⊣ UY) (gx : LX ⊣ RX) (gy : LY ⊣ RY)
    (theta : LX ⋙ TX ≅ TY ⋙ LY) (K : A) :
    (Adjunction.pushHomOfComapIso ax ay
      (conjugateIsoEquiv (ay.comp gy) (gx.comp ax) theta)).app K =
    gy.homEquiv _ _ (theta.inv.app (RX.obj K) ≫ TX.map (gx.counit.app K)) := by
  have h := iterated_mateEquiv_conjugateEquiv_symm gx gy ay ax
    (TwoSquare.mk _ _ _ _
      (conjugateIsoEquiv (ay.comp gy) (gx.comp ax) theta).inv)
  rw [conjugateIsoEquiv_apply_inv] at h
  change (mateEquiv gx gy).symm
      ((mateEquiv ax ay).symm (TwoSquare.mk _ _ _ _
        ((conjugateEquiv (gx.comp ax) (ay.comp gy)) theta.inv))) =
    TwoSquare.mk _ _ _ _ ((conjugateEquiv (gx.comp ax) (ay.comp gy)).symm
      ((conjugateEquiv (gx.comp ax) (ay.comp gy)) theta.inv)) at h
  rw [Equiv.symm_apply_apply] at h
  have hh := congrArg (mateEquiv gx gy) h
  rw [Equiv.apply_symm_apply] at hh
  have he := congrArg (fun s ↦ s.app K) hh
  simp only [Adjunction.pushHomOfComapIso, conjugateIsoEquiv_apply_inv,
    mateEquiv_apply, TwoSquare.mk, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.rightUnitor_inv_app,
    Functor.leftUnitor_hom_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.comp_obj, Functor.comp_map, Adjunction.homEquiv_unit, Functor.map_comp,
    Category.id_comp] at he ⊢
  repeat erw [Category.comp_id] at he
  exact he

private theorem exactDerivedAdj
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X S : Scheme.{u}} (f : X ⟶ S) :
    (CondensedRing.upperStarLowerStarAdjunction Λ f).mapDerivedCategoryRightDerivedAdjunction =
      (CondensedRing.derivedUpperStarLowerStarAdjunction Λ f).ofNatIsoLeft
        (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ f) := by
  unfold CondensedRing.derivedUpperStarLowerStarAdjunction
    CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory
  refine Adjunction.derived_eq_ofNatIsoLeft
    ((CondensedRing.upperStarLowerStarAdjunction Λ f).mapHomotopyCategory (.up ℤ))
      (HomotopyCategory.quasiIso _ (.up ℤ)) (HomotopyCategory.quasiIso _ (.up ℤ)) _ _ _
      (CondensedRing.upperStar Λ f).leftDerivedFunctorIsoMapDerivedCategory.symm ?_
  ext K
  simp only [Iso.symm_hom, NatTrans.comp_app, Functor.whiskerLeft_app]
  rw [← (CondensedRing.upperStar Λ f).leftDerivedFunctorIsoMapDerivedCategory_hom_fac]
  rw [NatTrans.comp_app, Functor.whiskerLeft_app, Iso.inv_hom_id_app_assoc]

section ModelComparison
universe b
variable {A : Type a} {B : Type b} [Category.{v} A] [Category.{w} B]
  [Abelian A] [Abelian B] [HasDerivedCategory A] [HasDerivedCategory B]
  [Abelian.HasKInjectiveResolutions A]
  (F : A ⥤ B) [F.Additive]

private def modelIso (R : DiagonalRightDerived F) : F.rightDerivedFunctor ≅ R.R := by
  let := R.universal
  let := canonicalDiagonalUnit_universal F
  exact Functor.rightDerivedUnique _ _ (canonicalDiagonalUnit F) R.η
    (HomologicalComplex.quasiIso A (.up ℤ))

private theorem modelIso_fac (R : DiagonalRightDerived F) (P : CochainComplex A ℤ) :
    F.rightDerivedFunctorUnitQ P ≫ (modelIso F R).hom.app (DerivedCategory.Q.obj P) =
      R.η.app P := by
  let := R.universal
  let := canonicalDiagonalUnit_universal F
  simpa only [canonicalDiagonalUnit, modelIso, Functor.rightDerivedUnique,
    Functor.rightDerivedNatIso_hom,
    Iso.refl_hom, NatTrans.id_app, Category.id_comp] using
    Functor.rightDerivedNatTrans_app F.rightDerivedFunctor R.R
      (canonicalDiagonalUnit F) R.η (HomologicalComplex.quasiIso A (.up ℤ))
      (𝟙 _) P
end ModelComparison

private theorem pushHom_modelIso
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L : A ⥤ B} {U : B ⥤ A} {L' : C ⥤ D} {U' : D ⥤ C}
    (adj : L ⊣ U) (adj' : L' ⊣ U') {G G' : A ⥤ C} {H : B ⥤ D}
    (κ : H ⋙ U' ≅ U ⋙ G) (e : G ≅ G') (K : A) :
    (Adjunction.pushHomOfComapIso adj adj'
      (κ ≪≫ Functor.isoWhiskerLeft U e)).app K =
      L'.map (e.inv.app K) ≫ (Adjunction.pushHomOfComapIso adj adj' κ).app K := by
  have h₀ := unit_mateEquiv_symm adj adj' (TwoSquare.mk _ _ _ _ κ.inv) K
  change G.map (adj.unit.app K) ≫ κ.inv.app (L.obj K) =
    adj'.unit.app (G.obj K) ≫
      U'.map ((Adjunction.pushHomOfComapIso adj adj' κ).app K) at h₀
  have h₁ := unit_mateEquiv_symm adj adj'
    (TwoSquare.mk _ _ _ _ (κ ≪≫ Functor.isoWhiskerLeft U e).inv) K
  change G'.map (adj.unit.app K) ≫
      (κ ≪≫ Functor.isoWhiskerLeft U e).inv.app (L.obj K) =
    adj'.unit.app (G'.obj K) ≫ U'.map
      ((Adjunction.pushHomOfComapIso adj adj'
        (κ ≪≫ Functor.isoWhiskerLeft U e)).app K) at h₁
  apply (adj'.homEquiv (G'.obj K) (H.obj (L.obj K))).injective
  rw [adj'.homEquiv_naturality_left, adj'.homEquiv_unit, adj'.homEquiv_unit]
  rw [← h₁, ← h₀]
  simpa only [Iso.trans_inv, NatTrans.comp_app, Functor.isoWhiskerLeft_inv,
    Functor.whiskerLeft_app, Functor.comp_obj, Functor.id_obj, Category.assoc] using
    congrArg (fun k ↦ k ≫ κ.inv.app (L.obj K)) (e.inv.naturality (adj.unit.app K))

private theorem pushHom_modelIso_isIso
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L : A ⥤ B} {U : B ⥤ A} {L' : C ⥤ D} {U' : D ⥤ C}
    (adj : L ⊣ U) (adj' : L' ⊣ U') {G G' : A ⥤ C} {H : B ⥤ D}
    (κ : H ⋙ U' ≅ U ⋙ G) (e : G ≅ G') (K : A)
    [IsIso ((Adjunction.pushHomOfComapIso adj adj' κ).app K)] :
    IsIso ((Adjunction.pushHomOfComapIso adj adj'
      (κ ≪≫ Functor.isoWhiskerLeft U e)).app K) := by
  rw [pushHom_modelIso]
  infer_instance

private theorem mate_of_push
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L : A ⥤ B} {U : B ⥤ A} {L' : C ⥤ D} {U' : D ⥤ C}
    {G : A ⥤ C} {H : B ⥤ D} (ax : L ⊣ U) (ay : L' ⊣ U')
    (e : H ⋙ U' ≅ U ⋙ G) (s : G ⋙ L' ⟶ L ⋙ H)
    (h : s = Adjunction.pushHomOfComapIso ax ay e) :
    mateEquiv ax ay (TwoSquare.mk G L L' H s) = TwoSquare.mk U H G U' e.inv := by
  rw [h]
  exact Equiv.apply_symm_apply (mateEquiv ax ay) _

section ScalarData
open CondensedRing IntegralFiniteScalar
attribute [local irreducible] IntegralFiniteScalar.geometricAdjunction
  CondensedRing.derivedComapUpperStarIso
  CondensedRing.derivedUpperStarLowerStarAdjunction
  CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory
  RestrictionSquare.mate
variable {Λ Λ' : ScalarSixRing.{u}} (D : ScalarSixPullbackData.{u}) (a : Λ ⟶ Λ')
  {X Y : Scheme.{u}} (f : X ⟶ Y)

private def exactScalarAdj (Z : Scheme.{u}) :
    scalarSixChange a Z ⊣ restriction a Z := scalarAdjunction a Z

private theorem restrictionPush_mate :
    (restrictionPush D a f).hom =
      (mateEquiv (geometricAdjunction Λ' f) (geometricAdjunction Λ f)
        (TwoSquare.mk (restriction a Y) (scalarSixPull Λ' f)
          (scalarSixPull Λ f) (restriction a X)
          (derivedComapUpperStarIso (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom f).inv)) := by
  have hn : (D.theta a f).hom = Adjunction.pushHomOfComapIso
      (exactScalarAdj a Y) (exactScalarAdj a X)
      (derivedComapUpperStarIso (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom f) := by
    simpa only [scalarSixPullHom, exactScalarAdj] using D.thetaNormalization a f
  have htheta := mate_of_push (exactScalarAdj a Y) (exactScalarAdj a X)
    (derivedComapUpperStarIso (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom f)
    (D.theta a f).hom hn
  have h := iterated_mateEquiv_conjugateEquiv
    (exactScalarAdj a Y) (exactScalarAdj a X)
    (geometricAdjunction Λ f) (geometricAdjunction Λ' f)
    (TwoSquare.mk (scalarSixPull Λ f) (scalarSixChange a Y)
      (scalarSixChange a X) (scalarSixPull Λ' f) (D.theta a f).hom)
  exact h.symm.trans (congrArg (fun s ↦
    (mateEquiv (geometricAdjunction Λ' f) (geometricAdjunction Λ f) s)) htheta)

private theorem restrictionPush_mate_exact :
    (mateEquiv
      (Adjunction.mapDerivedCategoryRightDerivedAdjunction
        (CondensedRing.upperStarLowerStarAdjunction Λ'.X f))
      (Adjunction.mapDerivedCategoryRightDerivedAdjunction
        (CondensedRing.upperStarLowerStarAdjunction Λ.X f))
      (TwoSquare.mk (restriction a Y) (scalarSixPull Λ' f)
      (scalarSixPull Λ f) (restriction a X)
      (derivedComapUpperStarIso (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom f).inv)) =
    (restrictionPush D a f).hom := by
  rw [restrictionPush_mate]
  unfold geometricAdjunction
  rw [exactDerivedAdj, exactDerivedAdj]
  rfl

private theorem restrictionPull_inv :
    ((Functor.mapDerivedCategoryCompIso
      (Mod.comap (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom Y))
      (CondensedRing.upperStar Λ.X f)) ≪≫
      Functor.mapDerivedCategoryNatIso
        (comapUpperStarIso (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom f).symm ≪≫
      (Functor.mapDerivedCategoryCompIso (CondensedRing.upperStar Λ'.X f)
        (Mod.comap (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom X))).symm).hom =
    (derivedComapUpperStarIso (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom f).inv := by
  simp only [derivedComapUpperStarIso, Iso.trans_inv, Iso.symm_inv,
    Iso.trans_hom, Iso.symm_hom, Functor.mapDerivedCategoryNatIso_symm, Category.assoc]

private def dataSquare : RestrictionSquare (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom f
    (canonicalDiagonalRightDerived (CondensedRing.lowerStar Λ.X f))
    (canonicalDiagonalRightDerived (CondensedRing.lowerStar Λ'.X f)) where
  iso := restrictionPush D a f
  normalization P := by
    have h := derived_mate_factors
      (CondensedRing.upperStarLowerStarAdjunction Λ'.X f)
      (CondensedRing.upperStarLowerStarAdjunction Λ.X f)
      (comapUpperStarIso (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom f).symm P
    simp only [Iso.symm_hom] at h
    rw [comapUpperStarIso_mate] at h
    have hm := restrictionPush_mate_exact D a f
    have hd := restrictionPull_inv a f
    simp only [hd] at h
    have hp := NatTrans.congr_app hm (DerivedCategory.Q.obj P)
    erw [hp] at h
    simpa only [canonicalDiagonalRightDerived, canonicalDiagonalUnit, chainDerivedUnit,
      Functor.rightDerivedFunctorUnitQ] using h

private theorem dataSquare_mate (K : DerivedCategory (Modules Λ.X X)) :
    ((dataSquare D a f).mate (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom).app K = gamma D a f K := by
  unfold RestrictionSquare.mate
  exact push_conjugate (scalarAdjunction a X) (scalarAdjunction a Y)
    (geometricAdjunction Λ f) (geometricAdjunction Λ' f) (D.theta a f) K

private def transportedDataSquare
    (R : DiagonalRightDerived (CondensedRing.lowerStar Λ.X f)) :
    RestrictionSquare (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom f R
      (canonicalDiagonalRightDerived (CondensedRing.lowerStar Λ'.X f)) where
  iso := (dataSquare D a f).iso ≪≫
    Functor.isoWhiskerLeft (restriction a X) (modelIso (CondensedRing.lowerStar Λ.X f) R)
  normalization P := by
    simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
      Functor.whiskerLeft_app, Category.assoc]
    rw [← (modelIso (CondensedRing.lowerStar Λ.X f) R).hom.naturality]
    have h := congrArg (fun k ↦ k ≫ (modelIso (CondensedRing.lowerStar Λ.X f) R).hom.app
      (DerivedCategory.Q.obj
        (((Mod.comap (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom X)).mapHomologicalComplex
          (.up ℤ)).obj P)))
      ((dataSquare D a f).normalization P)
    simpa only [Functor.comp_obj, Category.assoc, canonicalDiagonalRightDerived,
      canonicalDiagonalUnit, modelIso_fac] using h

private theorem mate_isIso_of_gamma
    (R : DiagonalRightDerived (CondensedRing.lowerStar Λ.X f))
    (s : RestrictionSquare (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom f R
      (canonicalDiagonalRightDerived (CondensedRing.lowerStar Λ'.X f)))
    (K : DerivedCategory (Modules Λ.X X)) [IsIso (gamma D a f K)] :
    IsIso ((s.mate (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom).app K) := by
  have hs : s.iso = (transportedDataSquare D a f R).iso :=
    square_unique (CondensedRing.lowerStar Λ'.X f) (CondensedRing.lowerStar Λ.X f)
      (Mod.comap (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom X))
      (Mod.comap (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom Y))
      (canonicalDiagonalRightDerived _) R
      (comapLowerStarIso (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom f) s _
  unfold RestrictionSquare.mate
  rw [hs]
  have hi : IsIso (((dataSquare D a f).mate (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom).app K) := by
    rw [dataSquare_mate]
    infer_instance
  have : IsIso ((Adjunction.pushHomOfComapIso (scalarAdjunction a X)
      (scalarAdjunction a Y) (dataSquare D a f).iso).app K) := by
    simpa only [RestrictionSquare.mate] using hi
  exact pushHom_modelIso_isIso (scalarAdjunction a X) (scalarAdjunction a Y)
    (dataSquare D a f).iso (modelIso (CondensedRing.lowerStar Λ.X f) R) K

end ScalarData

open CondensedRing IntegralFiniteScalar

private theorem restrictionReflectsIsomorphisms {Λ Λ' : ScalarSixRing.{u}}
    (a : Λ ⟶ Λ') (Z : Scheme.{u}) : (restriction a Z).ReflectsIsomorphisms := by
  let F : ModuleRingedComparison.internalModules Λ'.X Z ⥤
      ModuleRingedComparison.internalModules Λ.X Z :=
    Mod.comap (D := Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom Z)
  have : F.ReflectsIsomorphisms := by
    refine ⟨?_⟩
    intro M N f hf
    have : IsIso f.hom := by
      change IsIso ((Mod.forget (condensedRingObj Λ.X Z)).map (F.map f))
      infer_instance
    have : IsIso ((Mod.forget (condensedRingObj Λ'.X Z)).map f) := by
      change IsIso f.hom
      infer_instance
    exact isIso_of_reflects_iso f (Mod.forget (condensedRingObj Λ'.X Z))
  change F.mapDerivedCategory.ReflectsIsomorphisms
  refine ⟨fun g _ ↦ ?_⟩
  rw [DerivedCategory.isIso_iff]
  intro n
  have : IsIso (F.map ((DerivedCategory.homologyFunctor _ n).map g)) :=
    (NatIso.isIso_map_iff (F.mapDerivedCategoryHomologyFunctorIso n) g).2
      (by rw [Functor.comp_map]; infer_instance)
  exact isIso_of_reflects_iso _ F

/-- A finite free point resolution supplies a normalized restriction square and makes
the scalar mate of every full-unit-normalized restriction square invertible.
Source: current scalar-six direct-image proof, finite free
coefficient argument and formal properties; Stacks Tag 0944.
(blueprint: lem-diagonal-finite-resolution-scalar-mate).

Proof: the finite free derived comparison identifies restricted scalar extension with
tensoring by the specified cone. The actual mate becomes the projection map for this cone.
Projection is invertible on each finite free term, hence on the cone. Cancel the normalized
comparison isomorphisms and use conservativity of restriction. Full-unit normalization
uniquely determines the restriction square. Transport the canonical integral model to R
by the unique unit-preserving isomorphism; taking its scalar mate preserves invertibility.
-/
private theorem finiteFreePointResolution_scalarSquares
    {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')
    (P : ShortComplex (PointModules Λ))
    (t : P.X₃ ≅ (Mod.comap a.hom.hom).obj (Mod.regular Λ'.X))
    (hP : P.ShortExact) (r : ℕ)
    (e₁ : P.X₁ ≅ biproduct (fun _ : Fin r ↦ Mod.regular Λ.X))
    (e₂ : P.X₂ ≅ biproduct (fun _ : Fin r ↦ Mod.regular Λ.X))
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : DiagonalRightDerived (CondensedRing.lowerStar Λ.X f))
    : Nonempty (RestrictionSquare (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom f R
        (canonicalDiagonalRightDerived (CondensedRing.lowerStar Λ'.X f))) ∧
      ∀ (s : RestrictionSquare (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom f R
          (canonicalDiagonalRightDerived (CondensedRing.lowerStar Λ'.X f)))
        (K : DerivedCategory (Modules Λ.X X)),
        IsIso ((s.mate (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom).app K) := by
  obtain ⟨D⟩ := scalarSixPullbackData_exists.{u}
  refine ⟨⟨transportedDataSquare D a f R⟩, ?_⟩
  intro s K
  obtain ⟨hflat, β, hnorm, hpull, hmate⟩ :=
    derivedAssertions_of_finite_integral_resolution D a P t hP r e₁ e₂
  have hp := finiteFreeScalarProjection Λ P r e₁ e₂ f K
  have : (restriction a Y).ReflectsIsomorphisms := restrictionReflectsIsomorphisms a Y
  have hc : IsIso ((β Y).hom.app ((moduleObjectDerivedPushforward Λ.X f).obj K) ≫
      (restriction a Y).map (gamma D a f K) ≫
      (restrictionPush D a f).hom.app ((scalarSixChange a X).obj K) ≫
      (moduleObjectDerivedPushforward Λ.X f).map ((β X).inv.app K)) := by
    rw [hmate X Y f K]
    exact hp
  have hi : IsIso ((restriction a Y).map (gamma D a f K)) := by
    have htail := (isIso_comp_left_iff ((β Y).hom.app
      ((moduleObjectDerivedPushforward Λ.X f).obj K)) _).mp hc
    exact (isIso_comp_right_iff
      ((restriction a Y).map (gamma D a f K))
      ((restrictionPush D a f).hom.app ((scalarSixChange a X).obj K) ≫
        (moduleObjectDerivedPushforward Λ.X f).map ((β X).inv.app K))).mp
      (by simpa only [Category.assoc] using htail)
  have : IsIso (gamma D a f K) := isIso_of_reflects_iso _ (restriction a Y)
  exact mate_isIso_of_gamma D a f R s K

/-- A rank-one short exact point resolution supplies the normalized scalar squares.
Source: finite free coefficient argument in the current scalar-six direct-image proof.
(blueprint: lem-diagonal-finite-resolution-scalar-mate).

Proof: identify the regular terms with their Fin 1 biproducts and apply the proved
finite-free comparison. Its square is fixed by the full cochain-unit equation, and
its mate is the cone projection after exact conservative restriction of scalars.
The coefficients remain arbitrary commutative condensed rings; no arithmetic is used.
-/
theorem rankOnePointResolution_scalarSquares
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (a : Λ ⟶ Λ') [IsMonHom a]
    (h : ∃ P : ShortComplex (Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ),
      P.ShortExact ∧ Nonempty (P.X₁ ≅ Mod.regular Λ) ∧
        Nonempty (P.X₂ ≅ Mod.regular Λ) ∧
        Nonempty (P.X₃ ≅ (Mod.comap a).obj (Mod.regular Λ')))
    {X S : Scheme.{u}} (f : X ⟶ S)
    (R : DiagonalRightDerived (CondensedRing.lowerStar Λ f)) :
    Nonempty (RestrictionSquare a f R
        (canonicalDiagonalRightDerived (CondensedRing.lowerStar Λ' f))) ∧
      ∀ (s : RestrictionSquare a f R
          (canonicalDiagonalRightDerived (CondensedRing.lowerStar Λ' f)))
        (K : DerivedCategory (Modules Λ X)), IsIso ((s.mate a).app K) := by
  let P := h.choose
  let e₁ := h.choose_spec.2.1.some
  let e₂ := h.choose_spec.2.2.1.some
  let t := h.choose_spec.2.2.2.some
  let O : CondensedRing.ScalarSixRing.{u} := CommMon.mk Λ
  let A : CondensedRing.ScalarSixRing.{u} := CommMon.mk Λ'
  let b : O ⟶ A := CommMon.homMk (Mon.Hom.mk a)
  let e := (biproductUniqueIso (fun _ : Fin 1 ↦ Mod.regular Λ)).symm
  have hh := finiteFreePointResolution_scalarSquares (Λ := O) (Λ' := A)
    b P t h.choose_spec.1 1 (e₁ ≪≫ e) (e₂ ≪≫ e) (X := X) (Y := S) f R
  exact hh

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
