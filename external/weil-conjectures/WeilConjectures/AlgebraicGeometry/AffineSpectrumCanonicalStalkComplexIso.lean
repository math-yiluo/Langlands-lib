/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.AffineSpectrumCanonicalStalkRingCoordinates
public import WeilConjectures.AlgebraicGeometry.IsoPullbackStalkCohomology
import Mathlib.CategoryTheory.Adjunction.FullyFaithful
/-! # Explicit canonical spectrum chain coordinates -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ChangeOfRings
noncomputable section
namespace AlgebraicGeometry.SingleComplexBaseChange
variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
/-- Canonical chain transport: the extension/restriction unit followed by the inverse
pullback-stalk comparison. The latter is pinned by its formula on all section germs,
which generate the extension of scalars, so no arbitrary existence witness is chosen.
Source: Stacks Project, Tags 0098 and 0096.
(blueprint: def-pc-affine-spectrum-canonical-stalk-complex-iso). -/
def isoPullbackModuleStalkComplexIso
    {Y Z : Scheme.{u}} (j : Y ⟶ Z) [IsIso j] (y : Y)
    (P : CochainComplex Z.Modules ℤ) :
    ((((RingedSpace.moduleStalkFunctor Z.toRingedSpace (j y)).mapHomologicalComplex
        (.up ℤ)).obj P) ≅
      ((ModuleCat.restrictScalars (j.stalkMap y).hom).mapHomologicalComplex (.up ℤ)).obj
        (((RingedSpace.moduleStalkFunctor Y.toRingedSpace y).mapHomologicalComplex
          (.up ℤ)).obj
          (((Scheme.Modules.tensorPullback j).mapHomologicalComplex (.up ℤ)).obj P))) := by
  let ρ := (j.stalkMap y).hom
  let eρ := RingEquiv.ofBijective ρ
    (ConcreteCategory.bijective_of_isIso (j.stalkMap y))
  have : (ModuleCat.restrictScalars.{u} ρ).IsEquivalence :=
    ModuleCat.restrictScalars_isEquivalence_of_ringEquiv eρ
  let E := ModuleCat.extendScalars.{u} ρ
  let U := ModuleCat.restrictScalars.{u} ρ
  let S := RingedSpace.moduleStalkFunctor Z.toRingedSpace (j y)
  let T := Scheme.Modules.tensorPullback j ⋙ RingedSpace.moduleStalkFunctor Y.toRingedSpace y
  have : E.IsEquivalence :=
    (ModuleCat.extendRestrictScalarsAdj ρ).isEquivalence_left_of_isEquivalence_right
  let e := Classical.choose (Scheme.Modules.exists_tensorPullback_stalk_iso j y)
  let b : S ≅ T ⋙ U :=
    (Functor.rightUnitor S).symm ≪≫
      Functor.isoWhiskerLeft S (asIso (ModuleCat.extendRestrictScalarsAdj ρ).unit) ≪≫
      (Functor.associator S E U).symm ≪≫ Functor.isoWhiskerRight e.symm U
  have : (Scheme.Modules.tensorPullback j).Additive := tensorPullbackAdditive.{u, w} j
  have : (RingedSpace.moduleStalkFunctor Y.toRingedSpace y).Additive :=
    comparisonStalkAdditive Y y
  have : T.Additive := by dsimp [T]; infer_instance
  have hT : T.PreservesZeroMorphisms := by
    dsimp [T]
    have hp : (Scheme.Modules.tensorPullback j).PreservesZeroMorphisms := inferInstance
    have hs : (RingedSpace.moduleStalkFunctor Y.toRingedSpace y).PreservesZeroMorphisms :=
      inferInstance
    infer_instance
  have hU : U.PreservesZeroMorphisms := by dsimp [U]; infer_instance
  have hTU : (T ⋙ U).PreservesZeroMorphisms := inferInstance
  let q := (NatIso.mapHomologicalComplex b (.up ℤ)).app P
  exact q ≪≫
    (Functor.mapHomologicalComplexCompIso (Iso.refl (T ⋙ U)) (.up ℤ)).app P ≪≫
    ((U.mapHomologicalComplex (.up ℤ)).mapIso
      ((Functor.mapHomologicalComplexCompIso (Iso.refl T) (.up ℤ)).app P))

/-- The canonical chain transport with the source point identified by `h`.
Source: Stacks Project, Tags 0098 and 0096.
(blueprint: def-pc-affine-spectrum-canonical-stalk-complex-iso). -/
def canonicalSpectrumStalkComplexIso
  (X : Scheme.{u}) [IsAffine X] (x : X) (y : Spec Γ(X, ⊤))
  (h : x = X.isoSpec.inv y)
  (P : CochainComplex X.Modules ℤ) :
    ((((RingedSpace.moduleStalkFunctor X.toRingedSpace x).mapHomologicalComplex
        (.up ℤ)).obj P) ≅
      ((ModuleCat.restrictScalars
        (canonicalSpectrumStalkEquiv X x y h).toRingHom).mapHomologicalComplex
        (.up ℤ)).obj
        (((RingedSpace.moduleStalkFunctor
          (Spec Γ(X, ⊤)).toRingedSpace y).mapHomologicalComplex (.up ℤ)).obj
          (((Scheme.Modules.tensorPullback X.isoSpec.inv).mapHomologicalComplex
            (.up ℤ)).obj P))) := by
  subst x
  simpa only [canonicalSpectrumStalkEquiv, eqToIso_refl, Iso.refl_trans,
    RingEquiv.toRingHom_eq_coe, Iso.commRingCatIsoToRingEquiv_toRingHom, asIso_hom] using
    isoPullbackModuleStalkComplexIso X.isoSpec.inv y P

end AlgebraicGeometry.SingleComplexBaseChange
