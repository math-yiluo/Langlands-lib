/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedPullback
public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.AlgebraicGeometry.DerivedPullbackOpenRestrictionUniverses
import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Pullback from a supplied local K-flat model

## References

* Stacks Project, Tag 08DW, compatibility with open restriction, and Tag 06YJ
-/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace AlgebraicGeometry

attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

-- The restriction comparison uses independent localization universes.
/-- A K-flat model on an open computes pullback along a morphism factoring through it. -/
theorem derivedPullback_local_kFlat_model {T X : Scheme.{u}} (f : T ⟶ X)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings T.toRingedSpace))]
    (U : X.Opens)
    [HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (g : T ⟶ U.toScheme) (hcomp : g ≫ U.ι = f)
    (E : schemeDerivedCategory X)
    (K : CochainComplex (SheafOfModules.{u}
      ((moduleRings X.toRingedSpace).over U)) ℤ)
    (hK : CochainComplex.IsAcyclicTensorKFlat (R := U.toScheme.sheaf)
      (((Scheme.Modules.overEquiv U).functor.mapHomologicalComplex (.up ℤ)).obj K))
    (hmodel : Nonempty ((SheafOfModules.overFunctor.{u}
      (moduleRings X.toRingedSpace) U).mapDerivedCategory.obj E ≅
        DerivedCategory.Q.obj K)) :
    Nonempty ((derivedPullback f).obj E ≅ DerivedCategory.Q.obj
      ((Functor.mapHomologicalComplex
        ((Scheme.Modules.overEquiv U).functor ⋙ Scheme.Modules.pullback g) (.up ℤ)).obj K)) := by
  classical
  let W : T.Opens := ⊤
  let b := W.ι
  have hb : IsIso b := inferInstanceAs (IsIso T.topIso.hom)
  let := HasDerivedCategory.standard
    (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
  let := HasDerivedCategory.standard
    (SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace))
  let V : SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U) ⥤
      SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace) :=
    (Scheme.Modules.overEquiv U).functor
  let RX := SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U
  let RT : SheafOfModules.{u} (moduleRings T.toRingedSpace) ⥤
      SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace) :=
    SheafOfModules.overFunctor.{u} (moduleRings T.toRingedSpace) W ⋙
    (Scheme.Modules.overEquiv W).functor
  let et : SheafOfModules.{u} (moduleRings T.toRingedSpace) ≌
      SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace) := CategoryTheory.Equivalence.mk
    (Scheme.Modules.restrictFunctor b) (Scheme.Modules.restrictFunctor T.topIso.inv)
    ((Scheme.Modules.restrictFunctorId).symm ≪≫
      Scheme.Modules.restrictFunctorCongr (by simp [b, W]) ≪≫
      Scheme.Modules.restrictFunctorComp T.topIso.inv b)
    ((Scheme.Modules.restrictFunctorComp b T.topIso.inv).symm ≪≫
      Scheme.Modules.restrictFunctorCongr (by simp [b, W]) ≪≫
      Scheme.Modules.restrictFunctorId)
  have : (Scheme.Modules.restrictFunctor b).IsEquivalence := et.isEquivalence_functor
  have : RT.IsEquivalence :=
    Functor.isEquivalence_of_iso (Scheme.Modules.overFunctorEquiv W).symm
  have hUV : W ≤ f ⁻¹ᵁ U := by
    intro t ht
    change f t ∈ U
    rw [← hcomp]
    exact (g t).property
  let r := f.resLE U W hUV
  have hr : b ≫ g = r := by
    apply (cancel_mono U.ι).1
    rw [Category.assoc, hcomp, Scheme.Hom.resLE_comp_ι]
  have : V.Additive := Functor.additive_of_preserves_binary_products _
  let PR : SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace) ⥤
      SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace) := Scheme.Modules.pullback r
  have : PR.Additive := Scheme.Modules.instAdditivePullback r
  let PG : SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace) ⥤
      SheafOfModules.{u} (moduleRings T.toRingedSpace) := Scheme.Modules.pullback g
  have : PG.Additive := Scheme.Modules.instAdditivePullback g
  let P := (V.mapHomologicalComplex (.up ℤ)).obj K
  obtain ⟨m⟩ := hmodel
  let eP : (RX ⋙ V).mapDerivedCategory.obj E ≅ DerivedCategory.Q.obj P :=
    (Functor.mapDerivedCategoryCompIso RX V).symm.app E ≪≫
      V.mapDerivedCategory.mapIso m ≪≫ V.mapDerivedCategoryFactors.app K
  obtain ⟨θ⟩ := derivedPullback_openRestriction_iso_universes f W U hUV
  obtain ⟨I, hI, hImap, hIadd, hIlim, hIcolim, hIres,
    F, hF, hFmap, hFadd, ε, hL, htri, hflat⟩ :=
    (derivedPullback_spec r)
  let H : SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace) ⥤
      SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace) :=
    Scheme.Modules.tensorPullback r
  have hEq : F = H :=
    CategoryTheory.Functor.ext hF (fun _ _ a ↦ hFmap a)
  subst F
  have : IsIso (ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) := hflat P hK
  let τ : H ≅ PR :=
    (Scheme.Modules.nonempty_tensorPullbackAdjunction r).some.leftAdjointUniq
      (Scheme.Modules.pullbackPushforwardAdjunction r)
  let q : (derivedPullback r).obj (DerivedCategory.Q.obj P) ≅
      DerivedCategory.Q.obj
        ((PR.mapHomologicalComplex (.up ℤ)).obj P) :=
    (derivedPullback r).mapIso ((DerivedCategory.quotientCompQhIso _).app P).symm ≪≫
      asIso (ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) ≪≫
      (DerivedCategory.Qh (C := SheafOfModules.{u}
        (moduleRings W.toScheme.toRingedSpace))).mapIso
        ((H.mapHomotopyCategoryFactors (.up ℤ)).app P) ≪≫
      (DerivedCategory.quotientCompQhIso
        (SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace))).app _ ≪≫
      DerivedCategory.Q.mapIso ((NatIso.mapHomologicalComplex τ (.up ℤ)).app P)
  let left : RT.mapDerivedCategory.obj ((derivedPullback f).obj E) ≅
      DerivedCategory.Q.obj
        ((PR.mapHomologicalComplex (.up ℤ)).obj P) :=
    θ.app E ≪≫ (derivedPullback r).mapIso eP ≪≫ q
  let J : SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U) ⥤
      SheafOfModules.{u} (moduleRings T.toRingedSpace) := V ⋙ PG
  have : J.Additive := inferInstance
  let δ : J ⋙ RT ≅ V ⋙ Scheme.Modules.pullback r :=
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft V
        (Functor.isoWhiskerLeft (Scheme.Modules.pullback g)
          (Scheme.Modules.overFunctorEquiv W)) ≪≫
      Functor.isoWhiskerLeft V
        (Functor.isoWhiskerLeft (Scheme.Modules.pullback g)
          (Scheme.Modules.restrictFunctorIsoPullback b)) ≪≫
      Functor.isoWhiskerLeft V (Scheme.Modules.pullbackComp b g) ≪≫
      Functor.isoWhiskerLeft V (Scheme.Modules.pullbackCongr hr)
  let right : RT.mapDerivedCategory.obj
      (DerivedCategory.Q.obj ((J.mapHomologicalComplex (.up ℤ)).obj K)) ≅
      DerivedCategory.Q.obj
        ((PR.mapHomologicalComplex (.up ℤ)).obj P) :=
    RT.mapDerivedCategoryFactors.app _ ≪≫ DerivedCategory.Q.mapIso
      (((Functor.mapHomologicalComplexCompIso (Iso.refl (J ⋙ RT)) (.up ℤ)).app K).symm ≪≫
        (NatIso.mapHomologicalComplex δ (.up ℤ)).app K ≪≫
        (Functor.mapHomologicalComplexCompIso
          (Iso.refl (V ⋙ PR)) (.up ℤ)).app K)
  exact ⟨RT.mapDerivedCategory.preimageIso (left ≪≫ right.symm)⟩

end AlgebraicGeometry
