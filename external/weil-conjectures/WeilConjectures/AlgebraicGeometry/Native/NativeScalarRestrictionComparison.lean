/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Locally.LocallyFiniteCoefficientRingRealization
import WeilConjectures.AlgebraicGeometry.Native.NativeScalarForgetting
import WeilConjectures.SixFunctors.ProEtale.Adic.PadicIntModuleUpperStar
import WeilConjectures.CategoryTheory.ModuleObjects.ChangeOfScalarsSquare

/-! # Restriction of native modules after coefficient transport

## References

* Stacks Project, Tag 03EK, and the naturality clause of the coefficient-ring realization

## Implementation details

The pullback isomorphism is obtained by conjugating the direct-image comparison under the
native and condensed inverse-image adjunctions, using that both normalized comparison functors
are equivalences.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

private noncomputable abbrev internalComparison (ℓ : ℕ) [Fact ℓ.Prime]
    (T : Scheme.{u}) :=
  let θ := (locallyFiniteCoefficientRing_realization ℓ).choose
  letI (X : Scheme.{u}) : IsMonHom (θ X).hom :=
    (locallyFiniteCoefficientRing_realization ℓ).choose_spec.1 X
  AdicSheaf.forgetAb ℓ T ⋙ Mod.comap (θ T).hom

private instance internalComparison_equivalence (ℓ : ℕ) [Fact ℓ.Prime]
    (T : Scheme.{u}) : (internalComparison ℓ T).IsEquivalence := by
  have : (AdicSheaf.forgetAb ℓ T).IsEquivalence :=
    nativeScalarForgetting_isEquivalence ℓ T
  let θ := (locallyFiniteCoefficientRing_realization ℓ).choose
  let (X : Scheme.{u}) : IsMonHom (θ X).hom :=
    (locallyFiniteCoefficientRing_realization ℓ).choose_spec.1 X
  have : (Mod.comap (θ T).hom).IsEquivalence :=
    (Mod.comapEquivalenceOfIsIso (θ T).hom).isEquivalence_functor
  change (AdicSheaf.forgetAb ℓ T ⋙ Mod.comap (θ T).hom).IsEquivalence
  infer_instance

private noncomputable def nativePushforwardComparison (ℓ : ℕ) [Fact ℓ.Prime]
    {S T : Scheme.{u}} (h : S ⟶ T) :
    adicLowerStar ℓ h ⋙ internalComparison ℓ T ≅
      internalComparison ℓ S ⋙ CondensedRing.lowerStar (Profinite.padicAlgClRingObj ℓ) h := by
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
  let e₁ : adicLowerStar ℓ h ⋙ internalComparison ℓ T ≅
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
  let e₂ : internalComparison ℓ S ⋙
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

/-- The normalized abelian presentation of a native module commutes with restriction.
For `θ` the chosen coefficient-ring realization, native pullback along `h` followed by
forgetting scalars and restricting along `θ S` is isomorphic to forgetting scalars and
restricting along `θ T` followed by condensed pullback along `h`. -/
theorem nativeScalarForgetting_pullbackIso (ℓ : ℕ) [Fact ℓ.Prime]
    {S T : Scheme.{u}} (h : S ⟶ T) :
    let θ := (locallyFiniteCoefficientRing_realization ℓ).choose
    letI (X : Scheme.{u}) : IsMonHom (θ X).hom :=
      (locallyFiniteCoefficientRing_realization ℓ).choose_spec.1 X
    Nonempty (adicUpperStar ℓ h ⋙ AdicSheaf.forgetAb ℓ S ⋙ Mod.comap (θ S).hom ≅
      AdicSheaf.forgetAb ℓ T ⋙ Mod.comap (θ T).hom ⋙
        CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) h) := by
  dsimp only
  let Eₛ := (internalComparison ℓ S).asEquivalence
  let Eₜ := (internalComparison ℓ T).asEquivalence
  let c := Adjunction.pullIsoOfComapIso Eₛ.symm.toAdjunction Eₜ.symm.toAdjunction
    (CondensedRing.upperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ) h)
    (adicUpperStarLowerStarAdjunction ℓ h) (nativePushforwardComparison ℓ h)
  refine ⟨?_⟩
  exact Functor.isoWhiskerRight Eₜ.unitIso
      (adicUpperStar ℓ h ⋙ Eₛ.functor) ≪≫
    Functor.isoWhiskerLeft Eₜ.functor (Functor.isoWhiskerRight c.symm Eₛ.functor) ≪≫
    Functor.isoWhiskerLeft
      (Eₜ.functor ⋙ CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) h) Eₛ.counitIso

end AlgebraicGeometry.ProEtale
