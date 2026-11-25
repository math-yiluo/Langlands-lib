/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.Proper.Open.ProperOpenCoefficientRefinement
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekBaseChange
import WeilConjectures.CategoryTheory.Adjunction.SmoothPurity.OpenScalarExchangeMate
import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactScalarCoherence
import all WeilConjectures.AlgebraicGeometry.Proper.Open.ProperOpenCoefficientRefinement
import WeilConjectures.AlgebraicGeometry.Scalar.ScalarPullbackComposition
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-! # Scalar exchange for an arbitrary cartesian open square -/
@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

private theorem pullback_scalar_cube
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {U' U T' T : Scheme.{u}} {h : U' ⟶ U} {j' : U' ⟶ T'}
    {j : U ⟶ T} {g : T' ⟶ T} (sq : CommSq h j' j g)
    (M : DerivedCategoryModule A T) :
    (scalarExtension φ U').map
        ((exactDerivedSquareUpperStarIso (ModuleCat.{u + 1} A) sq.flip).hom.app M) ≫
      (properOpenCoefficientPullbackIso φ j').inv.app
        ((upperStar (ModuleCat.{u + 1} A) g).mapDerivedCategory.obj M) ≫
      (upperStar (ModuleCat.{u + 1} B) j').mapDerivedCategory.map
        ((properOpenCoefficientPullbackIso φ g).inv.app M) =
      (properOpenCoefficientPullbackIso φ h).inv.app
        ((upperStar (ModuleCat.{u + 1} A) j).mapDerivedCategory.obj M) ≫
      (upperStar (ModuleCat.{u + 1} B) h).mapDerivedCategory.map
        ((properOpenCoefficientPullbackIso φ j).inv.app M) ≫
      (exactDerivedSquareUpperStarIso (ModuleCat.{u + 1} B) sq.flip).hom.app
        ((scalarExtension φ T).obj M) := by
  let k (R : Type (u + 1)) [CommRing R] {V W Z : Scheme.{u}}
      (v : W ⟶ Z) (w : V ⟶ W) (t : V ⟶ Z) (ht : w ≫ v = t) :=
    Functor.mapDerivedCategoryNatIso
        (upperStarComp (ModuleCat.{u + 1} R) w v t ht.symm) ≪≫
      (Functor.mapDerivedCategoryCompIso _ _).symm
  have hc (R : Type (u + 1)) [CommRing R] :
      exactDerivedSquareUpperStarIso (ModuleCat.{u + 1} R) sq.flip =
        (k R j h (j' ≫ g) sq.w).symm ≪≫ k R g j' (j' ≫ g) rfl := by
    apply Iso.ext
    simp only [exactDerivedSquareUpperStarIso, squareUpperStarIso, k,
      Functor.mapDerivedCategoryNatIso_trans, Functor.mapDerivedCategoryNatIso_symm,
      Iso.trans_hom, Iso.symm_hom, Iso.symm_inv, Iso.trans_inv, Category.assoc]
  have h1 := coefficientPullback_comp φ j h (j' ≫ g) sq.w M
  have h2 := coefficientPullback_comp φ g j' (j' ≫ g) rfl M
  change (k B j h (j' ≫ g) sq.w).hom.app _ ≫ _ ≫ _ =
    _ ≫ (scalarExtension φ U').map ((k A j h (j' ≫ g) sq.w).hom.app M) at h1
  change (k B g j' (j' ≫ g) rfl).hom.app _ ≫ _ ≫ _ =
    _ ≫ (scalarExtension φ U').map ((k A g j' (j' ≫ g) rfl).hom.app M) at h2
  have hh : (exactDerivedSquareUpperStarIso (ModuleCat.{u + 1} B) sq.flip).hom.app
          ((scalarExtension φ T).obj M) ≫
        (upperStar (ModuleCat.{u + 1} B) j').mapDerivedCategory.map
          ((properOpenCoefficientPullbackIso φ g).hom.app M) ≫
        (properOpenCoefficientPullbackIso φ j').hom.app
          ((upperStar (ModuleCat.{u + 1} A) g).mapDerivedCategory.obj M) =
      (upperStar (ModuleCat.{u + 1} B) h).mapDerivedCategory.map
          ((properOpenCoefficientPullbackIso φ j).hom.app M) ≫
        (properOpenCoefficientPullbackIso φ h).hom.app
          ((upperStar (ModuleCat.{u + 1} A) j).mapDerivedCategory.obj M) ≫
        (scalarExtension φ U').map
          ((exactDerivedSquareUpperStarIso (ModuleCat.{u + 1} A) sq.flip).hom.app M) := by
    simp only [hc, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      Functor.map_comp, Category.assoc]
    rw [h2]
    apply (cancel_epi ((k B j h (j' ≫ g) sq.w).hom.app
      ((scalarExtension φ T).obj M))).1
    simp only [Iso.hom_inv_id_app_assoc]
    rw [reassoc_of% h1]
    simp only [← Functor.map_comp_assoc, Iso.hom_inv_id_app,
      CategoryTheory.Functor.map_id, Category.id_comp]
  have hh' := congrArg (fun z ↦
    (properOpenCoefficientPullbackIso φ h).inv.app
        ((upperStar (ModuleCat.{u + 1} A) j).mapDerivedCategory.obj M) ≫
    (upperStar (ModuleCat.{u + 1} B) h).mapDerivedCategory.map
      ((properOpenCoefficientPullbackIso φ j).inv.app M) ≫ z ≫
    (properOpenCoefficientPullbackIso φ j').inv.app
      ((upperStar (ModuleCat.{u + 1} A) g).mapDerivedCategory.obj M) ≫
    (upperStar (ModuleCat.{u + 1} B) j').mapDerivedCategory.map
      ((properOpenCoefficientPullbackIso φ g).inv.app M)) hh
  dsimp only [Functor.comp_obj] at hh'
  simp only [Category.assoc, ← Functor.map_comp_assoc, ← Functor.map_comp,
    Iso.hom_inv_id_app_assoc, Iso.inv_hom_id_app_assoc, Iso.hom_inv_id_app,
    Iso.inv_hom_id_app, Functor.comp_obj, CategoryTheory.Functor.map_id,
    Category.id_comp, Category.comp_id] at hh'
  exact hh'.symm

private theorem open_exchange_unit
    (A : Type (u + 1)) [CommRing A]
    {U' U T' T : Scheme.{u}} {h : U' ⟶ U} {j' : U' ⟶ T'}
    {j : U ⟶ T} {g : T' ⟶ T} [IsOpenImmersion j] [IsOpenImmersion j']
    (sq : IsPullback h j' j g) (M : DerivedCategoryModule A U) :
    (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j').unit.app
        ((upperStar (ModuleCat.{u + 1} A) h).mapDerivedCategory.obj M) ≫
      (upperStar (ModuleCat.{u + 1} A) j').mapDerivedCategory.map
        ((mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso
          (ModuleCat.{u + 1} A) sq).hom.app M) =
      (upperStar (ModuleCat.{u + 1} A) h).mapDerivedCategory.map
        ((derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j).unit.app M) ≫
      (exactDerivedSquareUpperStarIso (ModuleCat.{u + 1} A) sq.toCommSq.flip).hom.app
        ((openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory.obj M) := by
  exact Adjunction.mapDerivedCategoryAdjunction_mate
    (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j)
    (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j')
    (squareUpperStarIso (ModuleCat.{u + 1} A) sq.toCommSq.flip)
    (@asIso _ _ _ _ _ (isIso_openImmersionLowerShriekBaseChangeMap (ModuleCat.{u + 1} A) sq))
    (fun K ↦ unit_map_openImmersionLowerShriekBaseChangeMap_app
      (ModuleCat.{u + 1} A) sq.toCommSq K) M

/-- Open coefficient balancing commutes with every cartesian open square.
Source: Stacks 03S6, 07A4 (blueprint: lem-pur-open-scalar-exchange-square).
Proof: transpose the equality under the target open adjunction. The prescribed
unit equations for scalar balancing and open base change compute both transposes.
The scalar pullback cube, obtained by localization and mates of the ordinary
restriction-of-scalars cube, identifies them. This argument imposes no boundedness
or finiteness on the input or coefficients. -/
theorem properOpenCoefficientOpenInverse_baseChange
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {U' U T' T : Scheme.{u}} {h : U' ⟶ U} {j' : U' ⟶ T'}
    {j : U ⟶ T} {g : T' ⟶ T} [IsOpenImmersion j] [IsOpenImmersion j']
    (sq : IsPullback h j' j g) (M : DerivedCategoryModule A U) :
    (openImmersionLowerShriek (ModuleCat.{u + 1} B) j').mapDerivedCategory.map
        ((properOpenCoefficientPullbackIso φ h).inv.app M) ≫
      (mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso
        (ModuleCat.{u + 1} B) sq).hom.app ((scalarExtension φ U).obj M) ≫
      (upperStar (ModuleCat.{u + 1} B) g).mapDerivedCategory.map
        (properOpenCoefficientOpenInverse φ j M) =
      properOpenCoefficientOpenInverse φ j'
        ((upperStar (ModuleCat.{u + 1} A) h).mapDerivedCategory.obj M) ≫
      (scalarExtension φ T').map
        ((mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso
          (ModuleCat.{u + 1} A) sq).hom.app M) ≫
      (properOpenCoefficientPullbackIso φ g).inv.app
        ((openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory.obj M) := by
  have hi {W Z : Scheme.{u}} (k : W ⟶ Z) [IsOpenImmersion k]
      (N : DerivedCategoryModule A W) :
      (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B) k).unit.app
          ((scalarExtension φ W).obj N) ≫
        (upperStar (ModuleCat.{u + 1} B) k).mapDerivedCategory.map
          ((ExceptionalCoefficients.openIso φ k).inv.app N) =
        (scalarExtension φ W).map
          ((derivedOpenImmersionLowerShriekUpperStarAdjunction
            (ModuleCat.{u + 1} A) k).unit.app N) ≫
        (properOpenCoefficientPullbackIso φ k).inv.app
          ((openImmersionLowerShriek (ModuleCat.{u + 1} A) k).mapDerivedCategory.obj N) := by
    rw [compactScalarOpen_normalization]
    exact (derivedOpenImmersionLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} B) k).homEquiv _ _ |>.apply_symm_apply _
  have hc := pullback_scalar_cube φ sq.toCommSq
  have hh := Adjunction.openScalar_exchange_of_unit
    (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j)
    (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j')
    (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B) j)
    (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B) j')
    (upperStar (ModuleCat.{u + 1} A) h).mapDerivedCategory
    (upperStar (ModuleCat.{u + 1} B) h).mapDerivedCategory
    (upperStar (ModuleCat.{u + 1} A) g).mapDerivedCategory
    (upperStar (ModuleCat.{u + 1} B) g).mapDerivedCategory
    (scalarExtension φ U) (scalarExtension φ U')
    (scalarExtension φ T) (scalarExtension φ T')
    (properOpenCoefficientPullbackIso φ g) (properOpenCoefficientPullbackIso φ h)
    (properOpenCoefficientPullbackIso φ j) (properOpenCoefficientPullbackIso φ j')
    (exactDerivedSquareUpperStarIso (ModuleCat.{u + 1} A) sq.toCommSq.flip)
    (exactDerivedSquareUpperStarIso (ModuleCat.{u + 1} B) sq.toCommSq.flip)
    (ExceptionalCoefficients.openIso φ j).inv (ExceptionalCoefficients.openIso φ j').inv
    (mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso
      (ModuleCat.{u + 1} A) sq).hom
    (mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso
      (ModuleCat.{u + 1} B) sq).hom
    (hi j) (hi j') (open_exchange_unit A sq) (open_exchange_unit B sq) hc M
  simpa only [compactScalarOpen_normalization] using hh

end AlgebraicGeometry.Etale
