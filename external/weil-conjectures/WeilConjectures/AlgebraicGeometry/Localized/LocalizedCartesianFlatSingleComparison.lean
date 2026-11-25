/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import WeilConjectures.AlgebraicGeometry.LocalizedMixedDerivedPullback

import WeilConjectures.AlgebraicGeometry.Standard.StandardFlatSingleBaseChange
import WeilConjectures.AlgebraicGeometry.IsoPullbackStalkCohomology
import WeilConjectures.AlgebraicGeometry.DerivedDirectImageCompositionUnbounded
import WeilConjectures.AlgebraicGeometry.DerivedAdjoint
import WeilConjectures.AlgebraicGeometry.DerivedPullbackComposition
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived

/-! # Flat single base change on a cartesian source
-/

@[expose] public section
set_option autoImplicit false
universe u w wX wS wW wY
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry
attribute [local instance] Functor.additive_of_preserves_binary_products

private abbrev Mod (X : Scheme.{u}) :=
  SheafOfModules.{u} (moduleRings X.toRingedSpace)

private noncomputable def standardQIso (X : Scheme.{u})
    [h : HasDerivedCategory.{wX} (Mod X)] (K : CochainComplex (Mod X) ℤ) :
    (Localization.uniq (@DerivedCategory.Qh (Mod X) _ _ h)
      (@DerivedCategory.Qh (Mod X) _ _ (HasDerivedCategory.standard _))
      (HomotopyCategory.quasiIso (Mod X) (.up ℤ))).functor.obj
        (DerivedCategory.Q.obj K) ≅
      (@DerivedCategory.Q (Mod X) _ _ (HasDerivedCategory.standard _)).obj K := by
  let E := Localization.uniq (@DerivedCategory.Qh (Mod X) _ _ h)
    (@DerivedCategory.Qh (Mod X) _ _ (HasDerivedCategory.standard _))
    (HomotopyCategory.quasiIso (Mod X) (.up ℤ))
  exact E.functor.mapIso ((DerivedCategory.quotientCompQhIso (Mod X)).app K).symm ≪≫
    (Localization.compUniqFunctor (@DerivedCategory.Qh (Mod X) _ _ h)
      (@DerivedCategory.Qh (Mod X) _ _ (HasDerivedCategory.standard _))
      (HomotopyCategory.quasiIso (Mod X) (.up ℤ))).app
        ((HomotopyCategory.quotient (Mod X) (.up ℤ)).obj K) ≪≫
    (@DerivedCategory.quotientCompQhIso (Mod X) _ _ (HasDerivedCategory.standard _)).app K

private theorem standardDirectImageSingle {X Y : Scheme.{u}} (f : X ⟶ Y)
    [hx : HasDerivedCategory.{wX} (Mod X)]
    [hy : HasDerivedCategory.{wY} (Mod Y)] (M : (Mod X)) :
    Nonempty ((Localization.uniq (@DerivedCategory.Qh (Mod Y) _ _ hy)
      (@DerivedCategory.Qh (Mod Y) _ _ (HasDerivedCategory.standard _))
      (HomotopyCategory.quasiIso (Mod Y) (.up ℤ))).functor.obj
        ((schemeDerivedDirectImage f).obj ((DerivedCategory.singleFunctor (Mod X) 0).obj M)) ≅
      (@schemeDerivedDirectImage X Y (HasDerivedCategory.standard _)
        (HasDerivedCategory.standard _) f).obj
        ((@DerivedCategory.singleFunctor (Mod X) _ _
          (HasDerivedCategory.standard _) 0).obj M)) := by
  let K := (CochainComplex.singleFunctor (Mod X) 0).obj M
  let J := (CochainComplex.kInjectiveResolutionFunctor.{u} (Mod X)).obj K
  let s := (CochainComplex.toKInjectiveResolution.{u} (Mod X)).app K
  have : QuasiIso s := (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u}
    (Mod X) K).2
  obtain ⟨a⟩ := RingedSpace.derivedModuleDirectImage_computed_by_resolution
    f.toLRSHom.toShHom s
  obtain ⟨b⟩ := @RingedSpace.derivedModuleDirectImage_computed_by_resolution.{u, u + 1, u + 1}
    X.toRingedSpace Y.toRingedSpace
    (HasDerivedCategory.standard _) (HasDerivedCategory.standard _) f.toLRSHom.toShHom
    K J s inferInstance inferInstance
  let E := Localization.uniq (@DerivedCategory.Qh (Mod Y) _ _ hy)
    (@DerivedCategory.Qh (Mod Y) _ _ (HasDerivedCategory.standard _))
    (HomotopyCategory.quasiIso (Mod Y) (.up ℤ))
  exact ⟨E.functor.mapIso ((schemeDerivedDirectImage f).mapIso
      ((DerivedCategory.singleFunctorIsoCompQ (Mod X) 0).app M) ≪≫ a) ≪≫
    standardQIso Y _ ≪≫ b.symm ≪≫
    (@schemeDerivedDirectImage X Y (HasDerivedCategory.standard _)
      (HasDerivedCategory.standard _) f).mapIso
      ((@DerivedCategory.singleFunctorIsoCompQ (Mod X) _ _
        (HasDerivedCategory.standard _) 0).app M).symm⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem iso_pullback_computes {Y Y' : Scheme.{u}} (i : Y' ≅ Y)
    [HasDerivedCategory.{w} (Mod Y)]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y'.toRingedSpace))]
    (K : CochainComplex (Mod Y) ℤ) :
    Nonempty ((derivedPullback i.hom).obj (DerivedCategory.Q.obj K) ≅
      DerivedCategory.Q.obj
        (((Scheme.Modules.tensorPullback i.hom).mapHomologicalComplex (.up ℤ)).obj K)) := by
  let T : SheafOfModules.{u} (moduleRings Y.toRingedSpace) ⥤
      SheafOfModules.{u} (moduleRings Y'.toRingedSpace) :=
    Scheme.Modules.tensorPullback i.hom
  have : T.IsEquivalence :=
    SingleComplexBaseChange.tensorPullbackIsEquivalence i.hom
  have : T.Additive := Functor.additive_of_preserves_binary_products _
  obtain ⟨_, _, _, _, _, _, _, F, hF, hFmap, _, ε, hL, _, _⟩ :=
    (derivedPullback_spec i.hom)
  have h : F = T := CategoryTheory.Functor.ext hF (fun _ _ a ↦ hFmap a)
  subst F
  let W := HomotopyCategory.quasiIso
    (Mod Y) (.up ℤ)
  have : (derivedPullback i.hom).IsLeftDerivedFunctor ε W := hL
  have : T.mapDerivedCategory.IsLeftDerivedFunctor T.mapDerivedCategoryFactorsh.hom W :=
    Functor.isLeftDerivedFunctor_of_inverts _ _ T.mapDerivedCategoryFactorsh
  let compute := Functor.leftDerivedUnique T.mapDerivedCategory (derivedPullback i.hom) ε
    T.mapDerivedCategoryFactorsh.hom W
  exact ⟨compute.app (DerivedCategory.Q.obj K) ≪≫ T.mapDerivedCategoryFactors.app K⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in

private theorem standardCartesianFlatSingle
    {Y B Z A : Scheme.{u}} (p : Y ⟶ B) [QuasiCompact p] [QuasiSeparated p]
    (M : Y.Modules) [M.IsQuasicoherent] (hM : M.IsFlatOver p)
    (g : A ⟶ B) (q : Z ⟶ Y) (r : Z ⟶ A) (sq : IsPullback q r p g) :
    let := fun X : Scheme.{u} ↦ HasDerivedCategory.standard
      (Mod X)
    Nonempty ((schemeDerivedDirectImage r).obj
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) 0).obj
          (Scheme.Modules.tensorPullbackObj q M)) ≅
      (derivedPullback g).obj ((schemeDerivedDirectImage p).obj
        ((DerivedCategory.singleFunctor
          (Mod Y) 0).obj M))) := by
  classical
  let := fun X : Scheme.{u} ↦ HasDerivedCategory.standard
    (Mod X)
  obtain ⟨bc⟩ := standard_flat_single_baseChange p M hM g
  let i := sq.isoPullback
  obtain ⟨_, _, _, c, _, j, _⟩ := exists_derivedPullbackComposition
  let d₁ := c i.inv i.hom ≪≫
    eqToIso (congrArg (fun k ↦ derivedPullback k) i.inv_hom_id) ≪≫ j (pullback p g)
  let d₂ := c i.hom i.inv ≪≫
    eqToIso (congrArg (fun k ↦ derivedPullback k) i.hom_inv_id) ≪≫ j Z
  let di := CategoryTheory.Equivalence.mk
    (derivedPullback i.hom) (derivedPullback i.inv) d₁.symm d₂
  have : (derivedPullback i.hom).IsEquivalence := di.isEquivalence_functor
  obtain ⟨adj⟩ := nonempty_derivedPullbackAdjunction i.hom
  let N : Mod (pullback p g) := Scheme.Modules.tensorPullbackObj (pullback.fst p g) M
  let K := (CochainComplex.singleFunctor
    (SheafOfModules.{u} (moduleRings (pullback p g).toRingedSpace)) 0).obj N
  obtain ⟨compute⟩ := iso_pullback_computes i K
  let F : Mod (pullback p g) ⥤ Mod Z := Scheme.Modules.tensorPullback i.hom
  obtain ⟨cc⟩ := Scheme.Modules.nonempty_tensorPullbackComp i.hom (pullback.fst p g)
  let singleComp := DerivedCategory.Q.mapIso
    ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).app N) ≪≫
    ((DerivedCategory.singleFunctorIsoCompQ
      (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) 0).app (F.obj N)).symm
  let factor := (derivedPullback i.hom).mapIso
    ((DerivedCategory.singleFunctorIsoCompQ
      (SheafOfModules.{u} (moduleRings (pullback p g).toRingedSpace)) 0).app N) ≪≫
    compute ≪≫ singleComp ≪≫
    (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) 0).mapIso (cc.symm.app M)
  let push := (schemeDerivedDirectImage (pullback.snd p g)).mapIso
    ((asIso adj.unit).app ((DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings (pullback p g).toRingedSpace)) 0).obj N))
  obtain ⟨dc⟩ := derivedDirectImageComposition i.hom (pullback.snd p g)
  let transported := push ≪≫
    (dc.app ((derivedPullback i.hom).obj ((DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings (pullback p g).toRingedSpace)) 0).obj N))).symm ≪≫
    (schemeDerivedDirectImage (i.hom ≫ pullback.snd p g)).mapIso factor
  have hr : i.hom ≫ pullback.snd p g = r := sq.isoPullback_hom_snd
  have hq : i.hom ≫ pullback.fst p g = q := sq.isoPullback_hom_fst
  rw [hr, hq] at transported
  exact ⟨transported.symm ≪≫ bc⟩

/-- Flat single base change on a cartesian source. -/
theorem localized_cartesian_flat_single_comparison
    {S T Y Z : Scheme.{u}} (U : S.Opens) (V : U.toScheme.Opens) (W : T.Opens)
    [HasDerivedCategory.{wS}
      (SheafOfModules.{u} ((moduleRings U.toScheme.toRingedSpace).over V))]
    [HasDerivedCategory.{wW}
      (SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace))]
    [HasDerivedCategory.{wY}
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (p : Y ⟶ W.toScheme) [QuasiCompact p] [QuasiSeparated p]
    (M : Y.Modules) [M.IsQuasicoherent] (hM : M.IsFlatOver p)
    (g : V.toScheme ⟶ W.toScheme) (q : Z ⟶ Y) (r : Z ⟶ V.toScheme)
    (sq : IsPullback q r p g) :
  let dV := HasDerivedCategory.standard
    (SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace))
  letI := dV
  letI := HasDerivedCategory.standard
    (SheafOfModules.{u} (moduleRings Z.toRingedSpace))
  Nonempty ((@Functor.mapDerivedCategory _ _ _ dV _ _ _ _
      (Scheme.Modules.overEquiv V).inverse _ _ _).obj
      ((schemeDerivedDirectImage r).obj ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) 0).obj
          (Scheme.Modules.tensorPullbackObj q M))) ≅
    (localizedMixedDerivedPullback U V W g).obj
      ((schemeDerivedDirectImage p).obj ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj M))) := by
  classical
  let K := (schemeDerivedDirectImage p).obj ((DerivedCategory.singleFunctor
    (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj M)
  let QW := DerivedCategory.Qh
    (C := SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace))
  obtain ⟨t⟩ := standardDirectImageSingle p M
  let dW := HasDerivedCategory.standard
    (SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace))
  let dV := HasDerivedCategory.standard
    (SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace))
  let := dV
  let := HasDerivedCategory.standard
    (SheafOfModules.{u} (moduleRings Z.toRingedSpace))
  let E := (Scheme.Modules.overEquiv V).inverse
  let ED := @Functor.mapDerivedCategory _ _ _ dV _ _ _ _ E _ _ _
  let L := @derivedPullback _ _ g dW dV
  let EW := (Localization.uniq QW (@DerivedCategory.Qh _ _ _ dW)
    (HomotopyCategory.quasiIso _ (.up ℤ))).functor
  change Nonempty (ED.obj ((schemeDerivedDirectImage r).obj
    ((DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) 0).obj
        (Scheme.Modules.tensorPullbackObj q M))) ≅ ED.obj (L.obj (EW.obj K)))
  obtain ⟨b⟩ := standardCartesianFlatSingle p M hM g q r sq
  exact ⟨ED.mapIso (b ≪≫ (L.mapIso t).symm)⟩

end AlgebraicGeometry
