/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ExceptionalCoefficients.ExceptionalCoefficientMaps
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjection
public import WeilConjectures.CategoryTheory.Monoidal.EtaleDerivedTensorSymmetrySupplement
import WeilConjectures.AlgebraicGeometry.Etale.Ordered.EtaleOrderedOpenProjectionScalar
import WeilConjectures.AlgebraicGeometry.Etale.Scalar.EtaleScalarPullbackCompactification

/-! # Scalar compatibility of the open part of compact-support projection -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
universe u
open CategoryTheory
namespace AlgebraicGeometry.Etale

set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] HasDerivedCategory.ofHasKInjectiveResolutions
  HasDerivedCategory.standard Functor.leftAdjoint Functor.rightAdjoint
  Functor.leftDerivedFunctor Functor.mapDerivedCategory upperStar openImmersionLowerShriek
  derivedTensor ProEtale.pbcFixedScalarExtension
attribute [local irreducible] derivedTensorSymmetry
  derivedOpenImmersionLowerShriekProjectionIso ExceptionalCoefficients.openIso
  ExceptionalCoefficients.tensorIso scalarPullbackIso leftDerivedUpperStarCompactificationIso
  leftDerivedUpperStarComp leftDerivedUpperStarIsoMapDerivedCategory
  Functor.leftDerivedFunctorIsoMapDerivedCategory

/-- The ordered open projection followed by the compactification pullback comparison.
Source: Stacks 0GL6, projection formula preceding change of rings
(blueprint: lem-pur-etale-open-scalar-projection). -/
@[irreducible] def compactOpenProjection (R : Type (u + 1)) [CommRing R]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : DerivedCategoryModule R Y) (M : DerivedCategoryModule R X) :
    ((derivedTensor (ModuleCat.{u + 1} R) c.Z).obj
        ((upperStar (ModuleCat.{u + 1} R) c.g).leftDerivedFunctor.obj K)).obj
        ((openImmersionLowerShriek (ModuleCat.{u + 1} R) c.i).mapDerivedCategory.obj M) ⟶
      (openImmersionLowerShriek (ModuleCat.{u + 1} R) c.i).mapDerivedCategory.obj
        (((derivedTensor (ModuleCat.{u + 1} R) X).obj
          ((upperStar (ModuleCat.{u + 1} R) f).leftDerivedFunctor.obj K)).obj M) :=
  ((derivedTensorSymmetry (ModuleCat.{u + 1} R) c.Z).inv.app
      ((openImmersionLowerShriek (ModuleCat.{u + 1} R) c.i).mapDerivedCategory.obj M)).app
      ((upperStar (ModuleCat.{u + 1} R) c.g).leftDerivedFunctor.obj K) ≫
    ((derivedOpenImmersionLowerShriekProjectionIso (ModuleCat.{u + 1} R) c.i).inv.app
      M).app ((upperStar (ModuleCat.{u + 1} R) c.g).leftDerivedFunctor.obj K) ≫
    (openImmersionLowerShriek (ModuleCat.{u + 1} R) c.i).mapDerivedCategory.map
      (((derivedTensor (ModuleCat.{u + 1} R) X).obj M).map
        ((leftDerivedUpperStarCompactificationIso (ModuleCat.{u + 1} R) c).hom.app K)) ≫
    (openImmersionLowerShriek (ModuleCat.{u + 1} R) c.i).mapDerivedCategory.map
      (((derivedTensorSymmetry (ModuleCat.{u + 1} R) X).hom.app M).app
        ((upperStar (ModuleCat.{u + 1} R) f).leftDerivedFunctor.obj K))

private theorem scalarTensor_naturality
    {C D : Type*} [Category C] [Category D]
    (T : C ⥤ C ⥤ C) (U : D ⥤ D ⥤ D) (Q : C ⥤ D)
    (δ : Functor.uncurry.obj T ⋙ Q ≅ Q.prod Q ⋙ Functor.uncurry.obj U)
    {P P' : C} (a : P ⟶ P') (M : C) :
    Q.map ((T.map a).app M) ≫ δ.hom.app (P', M) =
      δ.hom.app (P, M) ≫ (U.map (Q.map a)).app (Q.obj M) := by
  have h := δ.hom.naturality (show (P, M) ⟶ (P', M) from (a, 𝟙 M))
  simpa only [Functor.comp_map, Functor.prod_map, Functor.prod_obj,
    Functor.uncurry_obj_map, _root_.CategoryTheory.Functor.map_id, Category.comp_id] using h

private theorem orderedOpenProjection_naturality
    (R : Type (u + 1)) [CommRing R] {X Z : Scheme.{u}}
    (j : X ⟶ Z) [IsOpenImmersion j]
    {T T' : DerivedCategoryModule R Z} (a : T ⟶ T') (M : DerivedCategoryModule R X) :
    ((derivedTensor (ModuleCat.{u + 1} R) Z).map a).app
        ((openImmersionLowerShriek (ModuleCat.{u + 1} R) j).mapDerivedCategory.obj M) ≫
      orderedOpenProjection R j T' M =
    orderedOpenProjection R j T M ≫
      (openImmersionLowerShriek (ModuleCat.{u + 1} R) j).mapDerivedCategory.map
        (((derivedTensor (ModuleCat.{u + 1} R) X).map
          ((upperStar (ModuleCat.{u + 1} R) j).leftDerivedFunctor.map a)).app M) := by
  have h₁ := ((derivedTensorSymmetry (ModuleCat.{u + 1} R) Z).inv.app
    ((openImmersionLowerShriek (ModuleCat.{u + 1} R) j).mapDerivedCategory.obj M)).naturality a
  simp only [Functor.flip_obj_map] at h₁
  have h₂ := ((derivedOpenImmersionLowerShriekProjectionIso
    (ModuleCat.{u + 1} R) j).inv.app M).naturality a
  change ((derivedTensor (ModuleCat.{u + 1} R) Z).obj
      ((openImmersionLowerShriek (ModuleCat.{u + 1} R) j).mapDerivedCategory.obj M)).map a ≫
      ((derivedOpenImmersionLowerShriekProjectionIso (ModuleCat.{u + 1} R) j).inv.app M).app
        T' =
    ((derivedOpenImmersionLowerShriekProjectionIso (ModuleCat.{u + 1} R) j).inv.app M).app T ≫
      (openImmersionLowerShriek (ModuleCat.{u + 1} R) j).mapDerivedCategory.map
        (((derivedTensor (ModuleCat.{u + 1} R) X).obj M).map
          ((upperStar (ModuleCat.{u + 1} R) j).leftDerivedFunctor.map a)) at h₂
  unfold orderedOpenProjection
  simp only [Category.assoc]
  rw [reassoc_of% h₁, reassoc_of% h₂]
  rw [← (openImmersionLowerShriek (ModuleCat.{u + 1} R) j).mapDerivedCategory.map_comp,
    ← (openImmersionLowerShriek (ModuleCat.{u + 1} R) j).mapDerivedCategory.map_comp]
  have h₃ := ((derivedTensorSymmetry (ModuleCat.{u + 1} R) X).hom.app M).naturality
    ((upperStar (ModuleCat.{u + 1} R) j).leftDerivedFunctor.map a)
  simp only [Functor.flip_obj_map] at h₃
  rw [h₃]

private theorem compactOpenProjection_factor
    (R : Type (u + 1)) [CommRing R]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : DerivedCategoryModule R Y) (M : DerivedCategoryModule R X) :
    compactOpenProjection R c K M =
      orderedOpenProjection R c.i
          ((upperStar (ModuleCat.{u + 1} R) c.g).leftDerivedFunctor.obj K) M ≫
        (openImmersionLowerShriek (ModuleCat.{u + 1} R) c.i).mapDerivedCategory.map
          (((derivedTensor (ModuleCat.{u + 1} R) X).map
            ((leftDerivedUpperStarCompactificationIso (ModuleCat.{u + 1} R) c).hom.app K)).app
              M) := by
  unfold compactOpenProjection orderedOpenProjection
  simp only [Category.assoc]
  rw [← (openImmersionLowerShriek (ModuleCat.{u + 1} R) c.i).mapDerivedCategory.map_comp,
    ← (openImmersionLowerShriek (ModuleCat.{u + 1} R) c.i).mapDerivedCategory.map_comp]
  have h := ((derivedTensorSymmetry (ModuleCat.{u + 1} R) X).hom.app M).naturality
    ((leftDerivedUpperStarCompactificationIso (ModuleCat.{u + 1} R) c).hom.app K)
  simp only [Functor.flip_obj_map] at h
  rw [h]
  simp only [Functor.comp_obj]

private theorem compactPullback_tensor_scalar
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : DerivedCategoryModule A Y) (M : DerivedCategoryModule A X) :
    let QX := scalarExtension φ X
    let TA := derivedTensor (ModuleCat.{u + 1} A) X
    let TB := derivedTensor (ModuleCat.{u + 1} B) X
    let T := (upperStar (ModuleCat.{u + 1} A) c.g).leftDerivedFunctor.obj K
    let aA := (leftDerivedUpperStarCompactificationIso (ModuleCat.{u + 1} A) c).hom.app K
    let aB := (leftDerivedUpperStarCompactificationIso (ModuleCat.{u + 1} B) c).hom.app
      ((scalarExtension φ Y).obj K)
    let b := (scalarPullbackIso φ c.g).inv.app K
    QX.map ((TA.map aA).app M) ≫
      (ExceptionalCoefficients.tensorIso φ X).hom.app
        ((upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj K, M) ≫
      (TB.map ((scalarPullbackIso φ f).inv.app K)).app (QX.obj M) =
    (ExceptionalCoefficients.tensorIso φ X).hom.app
        ((upperStar (ModuleCat.{u + 1} A) c.i).leftDerivedFunctor.obj T, M) ≫
      (TB.map ((scalarPullbackIso φ c.i).inv.app T)).app (QX.obj M) ≫
      (TB.map ((upperStar (ModuleCat.{u + 1} B) c.i).leftDerivedFunctor.map b)).app
        (QX.obj M) ≫
      (TB.map aB).app (QX.obj M) := by
  dsimp only
  have ht := scalarTensor_naturality
    (derivedTensor (ModuleCat.{u + 1} A) X)
    (derivedTensor (ModuleCat.{u + 1} B) X) (scalarExtension φ X)
    (ExceptionalCoefficients.tensorIso φ X)
    ((leftDerivedUpperStarCompactificationIso (ModuleCat.{u + 1} A) c).hom.app K) M
  have hp := scalarPullback_compactification φ c K
  rw [← Category.assoc, ht, Category.assoc, ← NatTrans.comp_app,
    ← (derivedTensor (ModuleCat.{u + 1} B) X).map_comp]
  rw [hp]
  simp only [Functor.map_comp, NatTrans.comp_app, Functor.comp_obj]

/-- Scalar compatibility of the open tensor map and composite pullback identification.
Source: Stacks 0GL6 and 07A4; compact-scalar coherence proof step 2, open part.
(blueprint: lem-pur-etale-open-scalar-projection).
Proof: use the mixed open scalar/tensor square of etaleOpenScalarComparisons.
Its scalar open comparison equals ExceptionalCoefficients.openIso by the
open-unit transpose normalization; its restriction comparison equals the exact
form of scalarPullbackIso. Invert the open projection and the scalar tensor
comparisons to put this equation in forward projection orientation. Transport
from exact restriction to left-derived inverse image through their canonical
comparison. The scalar/pullback composition equation for c.i and c.g, followed
by transport along c.comm, commutes with leftDerivedUpperStarCompactificationIso.
Paste these two squares and conjugate by the signed tensor symmetries. The
symmetry/scalar square holds on homogeneous flat K-flat tensors with the same
Koszul sign on each side and descends by localization. Thus the displayed
square holds for arbitrary K and M, including zero objects and the empty open;
no boundedness, flatness, or finite coefficient hypothesis is used. -/
theorem compactOpenProjection_scalarExtension
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : DerivedCategoryModule A Y) (M : DerivedCategoryModule A X) :
    (scalarExtension φ c.Z).map (compactOpenProjection A c K M) ≫
      (ExceptionalCoefficients.openIso φ c.i).hom.app
        (((derivedTensor (ModuleCat.{u + 1} A) X).obj
          ((upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj K)).obj M) ≫
      (openImmersionLowerShriek (ModuleCat.{u + 1} B) c.i).mapDerivedCategory.map
        ((ExceptionalCoefficients.tensorIso φ X).hom.app
            ((upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj K, M) ≫
          ((derivedTensor (ModuleCat.{u + 1} B) X).map
            ((scalarPullbackIso φ f).inv.app K)).app ((scalarExtension φ X).obj M)) =
    (ExceptionalCoefficients.tensorIso φ c.Z).hom.app
        ((upperStar (ModuleCat.{u + 1} A) c.g).leftDerivedFunctor.obj K,
          (openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategory.obj M) ≫
      ((derivedTensor (ModuleCat.{u + 1} B) c.Z).map
        ((scalarPullbackIso φ c.g).inv.app K)).app
          ((scalarExtension φ c.Z).obj
            ((openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategory.obj M)) ≫
      ((derivedTensor (ModuleCat.{u + 1} B) c.Z).obj
        ((upperStar (ModuleCat.{u + 1} B) c.g).leftDerivedFunctor.obj
          ((scalarExtension φ Y).obj K))).map
            ((ExceptionalCoefficients.openIso φ c.i).hom.app M) ≫
      compactOpenProjection B c ((scalarExtension φ Y).obj K)
        ((scalarExtension φ X).obj M) := by
  let JB := (openImmersionLowerShriek (ModuleCat.{u + 1} B) c.i).mapDerivedCategory
  let QX := scalarExtension φ X
  let TA := derivedTensor (ModuleCat.{u + 1} A) X
  let TB := derivedTensor (ModuleCat.{u + 1} B) X
  let T := (upperStar (ModuleCat.{u + 1} A) c.g).leftDerivedFunctor.obj K
  let aA := (leftDerivedUpperStarCompactificationIso (ModuleCat.{u + 1} A) c).hom.app K
  let aB := (leftDerivedUpperStarCompactificationIso (ModuleCat.{u + 1} B) c).hom.app
    ((scalarExtension φ Y).obj K)
  let b := (scalarPullbackIso φ c.g).inv.app K
  have hβ := (ExceptionalCoefficients.openIso φ c.i).hom.naturality ((TA.map aA).app M)
  simp only [Functor.comp_map] at hβ
  have hi := compactPullback_tensor_scalar φ c K M
  have ho := etaleOrderedOpenProjectionScalar φ c.i T M
  simp only [Functor.map_comp] at ho
  have hn := orderedOpenProjection_naturality B c.i b (QX.obj M)
  have hb := ((derivedTensor (ModuleCat.{u + 1} B) c.Z).map b).naturality
    ((ExceptionalCoefficients.openIso φ c.i).hom.app M)
  rw [compactOpenProjection_factor, compactOpenProjection_factor, Functor.map_comp]
  simp only [Category.assoc]
  rw [reassoc_of% hβ]
  rw [← JB.map_comp]
  rw [hi]
  simp only [JB.map_comp]
  rw [reassoc_of% ho]
  rw [← reassoc_of% hn]
  rw [reassoc_of% hb]

end AlgebraicGeometry.Etale
