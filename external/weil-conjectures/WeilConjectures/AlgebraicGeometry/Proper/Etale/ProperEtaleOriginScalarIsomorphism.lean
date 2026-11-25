/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Proper.Etale.ProperEtaleOriginScalarData
import WeilConjectures.AlgebraicGeometry.Etale.Origin.EtaleOriginScalarProjectionSquare
import WeilConjectures.AlgebraicGeometry.ProperTorsionProjectionFormula
import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.ProperProjectionFormula

/-! # Proper scalar comparison on bounded etale origins

## Main definitions and statement

- `properOriginTensorIso`: canonical constant-B tensor comparison.
- `properOriginMateIso`: the specified bounded-below direct-image mate.
- `properOriginEtaleProjection`: the actual etale projection arrow.
- `properEtaleOriginScalarIsomorphism`: invertibility and the restriction formula.

## References

* Stacks Project, Tag 0F0G
* Stacks Project, Tags 09A6, 0E48 and 0B56 (canonical comparison and scalar mate)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option maxRecDepth 2000
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale

attribute [local irreducible] Functor.mapDerivedCategory Functor.rightDerivedFunctor
  Etale.scalarTensorIso Scheme.completedAdicDerivedChange

private theorem properOriginEtaleProjection_isIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A]
    (φ : A →+* B) {Z Y : Scheme.{u}} (p : Z ⟶ Y) [IsProper p]
    (M : Etale.DerivedCategoryModule A Z) :
    IsIso (properOriginEtaleProjection φ p M) := by
  have : IsIso (((Etale.rightDerivedLowerStarProjectionMap
      (ModuleCat.{u + 1} A) p).app M).app (Etale.scalarCoefficient φ Y)) :=
    Etale.isIso_rightDerivedLowerStarProjectionMap_app_app_of_isProper_of_isAddTorsion
      A isAddTorsion_of_finite p M (Etale.scalarCoefficient φ Y)
  unfold properOriginEtaleProjection
  infer_instance

private theorem scalarMateRestriction_reflectsIso
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B) (Y : Scheme.{u}) :
    (scalarMateRestriction φ Y).mapDerivedCategory.ReflectsIsomorphisms := by
  let r := scalarMateRestriction φ Y
  have : PreservesFiniteLimits r :=
    (Scheme.proEtaleRingRestrictScalars_properties
      (Scheme.proEtaleConstantRingMap (T := Y) φ)).1
  have : PreservesFiniteColimits r :=
    (Scheme.proEtaleRingRestrictScalars_properties
      (Scheme.proEtaleConstantRingMap (T := Y) φ)).2.1
  have : r.ReflectsIsomorphisms :=
    (Scheme.proEtaleRingRestrictScalars_properties
      (Scheme.proEtaleConstantRingMap (T := Y) φ)).2.2
  refine ⟨fun f _ ↦ ?_⟩
  rw [DerivedCategory.isIso_iff]
  intro n
  have : IsIso (r.map ((DerivedCategory.homologyFunctor _ n).map f)) :=
    (NatIso.isIso_map_iff (r.mapDerivedCategoryHomologyFunctorIso n) f).2
      (by rw [Functor.comp_map]; infer_instance)
  exact isIso_of_reflects_iso _ r

/-- For proper `p`, the `B`-linear direct-image scalar comparison is invertible at a
bounded-below étale complex `E` whose tensor with `B` is bounded below, and it is given by
conjugating the étale projection with the origin mate isomorphisms and the tensor comparisons
`properOriginTensorIso`. -/
theorem properEtaleOriginScalarIsomorphism
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {Z Y : Scheme.{u}} (p : Z ⟶ Y) [IsProper p]
    (E : DerivedCategory.Plus
      (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} A))))
    (hH : ∃ n : ℤ,
      (properOriginEtaleTensor (RingHom.ulift.{u + 1, u + 1, u, u} φ) Z E.obj).IsGE n) :
    IsIso ((directImageScalarComparison φ p).app
      ((finiteCoefficientIntrinsicDerivedComparison Z A).obj E.obj)) ∧
    (scalarMateRestriction φ Y).mapDerivedCategory.map
        ((directImageScalarComparison φ p).app
          ((finiteCoefficientIntrinsicDerivedComparison Z A).obj E.obj)) ≫
      (scalarMateRestrictionPush φ p).hom.app
        ((directImageScalarExtension φ Z).obj
          ((finiteCoefficientIntrinsicDerivedComparison Z A).obj E.obj)) =
    (directImageScalarExtension φ Y ⋙ (scalarMateRestriction φ Y).mapDerivedCategory).map
        (properOriginMateIso A p E).inv ≫
      (properOriginTensorIso φ Y
        ((Etale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) p).rightDerivedFunctor.obj
          E.obj)).inv ≫
      (finiteCoefficientIntrinsicDerivedComparison Y A).map
        (properOriginEtaleProjection (RingHom.ulift.{u + 1, u + 1, u, u} φ) p E.obj) ≫
      (properOriginMateIso A p
        ⟨properOriginEtaleTensor (RingHom.ulift.{u + 1, u + 1, u, u} φ) Z E.obj, hH⟩).hom ≫
      (directImageConstantPush A p).map (properOriginTensorIso φ Z E.obj).hom := by
  let U := (scalarMateRestriction φ Y).mapDerivedCategory
  let S := directImageScalarExtension φ Y ⋙ U
  let M := (Etale.lowerStar
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) p).rightDerivedFunctor.obj E.obj
  let e := properOriginMateIso A p E
  let q := properOriginTensorIso φ Y M
  let χ := (directImageScalarComparison φ p).app
    ((finiteCoefficientIntrinsicDerivedComparison Z A).obj E.obj)
  let d := (scalarMateRestrictionPush φ p).hom.app
    ((directImageScalarExtension φ Z).obj
      ((finiteCoefficientIntrinsicDerivedComparison Z A).obj E.obj))
  have hs := etaleOriginScalarProjectionSquare φ p E hH
  have heq : U.map χ ≫ d =
      S.map e.inv ≫ q.inv ≫
        (finiteCoefficientIntrinsicDerivedComparison Y A).map
          (properOriginEtaleProjection (RingHom.ulift.{u + 1, u + 1, u, u} φ) p E.obj) ≫
        (properOriginMateIso A p
          ⟨properOriginEtaleTensor (RingHom.ulift.{u + 1, u + 1, u, u} φ) Z E.obj, hH⟩).hom ≫
        (directImageConstantPush A p).map (properOriginTensorIso φ Z E.obj).hom := by
    apply (cancel_epi (S.map e.hom)).1
    apply (cancel_epi q.hom).1
    simpa only [Category.assoc, ← S.map_comp_assoc, e.hom_inv_id,
      S.map_id, Category.id_comp, q.hom_inv_id_assoc] using hs
  have : IsIso (properOriginEtaleProjection
      (RingHom.ulift.{u + 1, u + 1, u, u} φ) p E.obj) :=
    properOriginEtaleProjection_isIso _ p E.obj
  have : IsIso (U.map χ ≫ d) := by
    rw [heq]
    infer_instance
  have : IsIso (U.map χ) := IsIso.of_isIso_comp_right _ d
  have : U.ReflectsIsomorphisms := scalarMateRestriction_reflectsIso φ Y
  exact ⟨isIso_of_reflects_iso χ U, heq⟩

end AlgebraicGeometry.ProEtale
