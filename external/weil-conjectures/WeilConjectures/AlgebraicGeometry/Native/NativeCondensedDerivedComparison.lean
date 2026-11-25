/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Native.NativeModuleConstructibilityComparison
public import WeilConjectures.AlgebraicGeometry.CondensedModuleDerivedPushpull
import WeilConjectures.AlgebraicGeometry.Native.NativeScalarRestrictionComparison
import WeilConjectures.AlgebraicGeometry.Native.NativeScalarForgetting
import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
import Mathlib.CategoryTheory.Triangulated.Subcategory
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
import WeilConjectures.SixFunctors.ProEtale.Adic.PadicIntModuleUpperStar
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategory

/-! # Exact native/condensed comparison and ordinary derived direct image
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- Forget ambient scalar linearity and transport the action along the normalized coefficient
isomorphism. This retains the underlying abelian sheaf and every section map. -/
abbrev nativeCondensedModules (l : ℕ) [Fact l.Prime] (T : Scheme.{u}) :=
  AdicSheaf.forgetAb l T ⋙ Mod.comap (nativeModuleCoefficientIso l T).hom

instance nativeCondensedModules_isEquivalence (l : ℕ) [Fact l.Prime] (T : Scheme.{u}) :
    (nativeCondensedModules l T).IsEquivalence := by
  have : (AdicSheaf.forgetAb l T).IsEquivalence :=
    nativeScalarForgetting_isEquivalence l T
  have : (Mod.comap (nativeModuleCoefficientIso l T).hom).IsEquivalence :=
    (Mod.comapEquivalenceOfIsIso (nativeModuleCoefficientIso l T).hom).isEquivalence_functor
  dsimp only [nativeCondensedModules]
  infer_instance

instance nativeCondensedModules_additive (l : ℕ) [Fact l.Prime] (T : Scheme.{u}) :
    (nativeCondensedModules l T).Additive := by
  refine { map_add := ?_ }
  intro X Y f g
  rfl

private noncomputable def nativeCondensedPushforwardIso (ℓ : ℕ) [Fact ℓ.Prime]
    {S T : Scheme.{u}} (h : S ⟶ T) :
    adicLowerStar ℓ h ⋙ nativeCondensedModules ℓ T ≅
      nativeCondensedModules ℓ S ⋙ CondensedRing.lowerStar (Profinite.padicAlgClRingObj ℓ) h := by
  let θ := (locallyFiniteCoefficientRing_realization ℓ).choose
  letI (X : Scheme.{u}) : IsMonHom (θ X).hom :=
    (locallyFiniteCoefficientRing_realization ℓ).choose_spec.1 X
  let L := lowerStar (WeilCoefficients.{u} ℓ) h
  let U := weilCoefficientsForgetAb ℓ T
  let V := weilCoefficientsForgetAb ℓ S
  let R := lowerStar Ab.{u + 1} h
  let B := adicConstantSheaf ℓ S
  let e := lowerStarCompWeilCoefficientsForgetAbIso ℓ h
  let a := (θ T).hom ≫ U.map (adicConstantSheafToLowerStar ℓ h)
  have ha : IsMonHom a := by dsimp [a]; infer_instance
  let e₁ : adicLowerStar ℓ h ⋙ nativeCondensedModules ℓ T ≅
      (V ⋙ R).mapMod B ⋙ Mod.comap
        ((θ T).hom ≫ U.map (adicConstantSheafToLowerStar ℓ h) ≫
          Functor.compAlgHom L U e.hom B) :=
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight
          (U.mapModComapIso (adicConstantSheafToLowerStar ℓ h)) _ ≪≫
        Functor.associator _ _ _) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (Functor.mapModCompIso L U e.hom B) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (Mod.comapComp _ _).symm _ ≪≫ (Mod.comapComp _ _).symm)
  let e₂ : nativeCondensedModules ℓ S ⋙
        CondensedRing.lowerStar (Profinite.padicAlgClRingObj ℓ) h ≅
      (V ⋙ R).mapMod B ⋙ Mod.comap
        (condensedPushforwardHom (Profinite.padicAlgClRingObj ℓ) h ≫ R.map (θ S).hom ≫
          Functor.compAlgHom V R (𝟙 (V ⋙ R)) B) :=
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (R.mapModComapIso (θ S).hom) _ ≪≫
        Functor.associator _ _ _) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (Functor.mapModCompIso V R (𝟙 (V ⋙ R)) B) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (Mod.comapComp _ _).symm _ ≪≫ (Mod.comapComp _ _).symm)
  refine e₁ ≪≫ Functor.isoWhiskerLeft _ (Mod.comapCongr ?_) ≪≫ e₂.symm
  simp only [Functor.compAlgHom, NatTrans.id_app]
  exact ((locallyFiniteCoefficientRing_realization ℓ).choose_spec.2.2 S T h).symm

/-- Exact transport also commutes with pullback. -/
theorem nativeCondensedPullbackIso (l : ℕ) [Fact l.Prime]
    {S T : Scheme.{u}} (f : S ⟶ T) :
    Nonempty (adicUpperStar l f ⋙ nativeCondensedModules l S ≅
      nativeCondensedModules l T ⋙ CondensedRing.upperStar (Profinite.padicAlgClRingObj l) f) :=
  nativeScalarForgetting_pullbackIso l f

/-- Deriving the direct-image square by its common K-injective model. -/
theorem nativeCondensedDerivedPushforwardIso (l : ℕ) [Fact l.Prime]
    {S T : Scheme.{u}} (f : S ⟶ T) :
    Nonempty ((adicLowerStar l f).rightDerivedFunctor ⋙
      (nativeCondensedModules l T).mapDerivedCategory ≅
      (nativeCondensedModules l S).mapDerivedCategory ⋙
        CondensedRing.moduleObjectDerivedPushforward (Profinite.padicAlgClRingObj l) f) := by
  let E := nativeCondensedModules l S
  exact ⟨(Functor.rightDerivedFunctorCompMapDerivedCategoryIso _ _).symm ≪≫
    Functor.rightDerivedFunctorNatIso (nativeCondensedPushforwardIso l f) ≪≫
    Functor.rightDerivedFunctorCompIso _ _ ≪≫
    Functor.isoWhiskerRight E.rightDerivedFunctorIsoMapDerivedCategory _⟩

/-- Exact pullback commutes with the normalized comparison, also after deriving. -/
theorem nativeCondensedDerivedPullbackIso (l : ℕ) [Fact l.Prime]
    {S T : Scheme.{u}} (f : S ⟶ T) :
    Nonempty ((adicUpperStar l f).mapDerivedCategory ⋙
        (nativeCondensedModules l S).mapDerivedCategory ≅
      (nativeCondensedModules l T).mapDerivedCategory ⋙
        CondensedRing.moduleObjectDerivedPullback (Profinite.padicAlgClRingObj l) f) := by
  exact ⟨Functor.mapDerivedCategoryCompIso _ _ ≪≫
    Functor.mapDerivedCategoryNatIso (nativeCondensedPullbackIso l f).some ≪≫
    (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.isoWhiskerLeft _ (Functor.leftDerivedFunctorIsoMapDerivedCategory
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) f)).symm⟩

/-- Constructibility is preserved by the normalized native/condensed comparison. -/
theorem nativeCondensed_constructible
    (k₀ k : Type u) [Field k₀] [Finite k₀] [Field k] [Algebra k₀ k]
    [IsAlgClosure k₀ k] (l : ℕ) [Fact l.Prime] (hl : l ≠ ringChar k₀)
    (T : Scheme.{u}) [T.Over (Spec (.of k))]
    [IsSeparated (T ↘ Spec (.of k))]
    [LocallyOfFiniteType (T ↘ Spec (.of k))] [QuasiCompact (T ↘ Spec (.of k))]
    (M : AdicSheaf l T) (hM : IsAdicConstructibleSheaf M) :
    IsConstantModelConstructible (Profinite.padicAlgClRingObj l) T
      ((nativeCondensedModules l T).obj M) := by
  obtain ⟨E, hE, _, _, _, _, hc, _⟩ :=
    nativeModuleConstructibilityComparison k₀ k l hl T
  have h := (hc M).mp hM
  rw [hE] at h
  have := (constantModelConstructibleFiniteTor_wellDefined
    (Profinite.padicAlgClRingObj l) T).1
  exact ObjectProperty.prop_of_iso _
    ((nativeOrdinaryPresentation l T).unitIso.symm.app
      ((nativeCondensedModules l T).obj M)) h

end AlgebraicGeometry.ProEtale
