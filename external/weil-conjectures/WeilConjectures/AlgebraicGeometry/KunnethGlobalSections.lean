/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Ordinary
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.SixFunctors.Etale.Derived.TensorStructure

/-!
# Canonical Künneth maps in module-valued global sections

Source: Stacks Project, Tag 0F1E; blueprint chap-Smooth-purity,
unit proposition-ordinary-external-kunneth--1 (blueprint: definition-kunneth-map--1).

The external product is the existing `kunnethMap`, transported by the canonical
constant-sheaf equivalence over a separably closed point and the Leray comparisons.
All comparisons below have explicit data; no isomorphism is chosen from `Nonempty`.

## Main definitions

- `pointGlobalSectionsTensorIso`: tensor comparison for evaluation at the base point.
- `kunnethGlobalSectionsMap`: the general-base `kunnethMap` in module-valued cohomology.
- `constantKunnethGlobalSectionsMap`: its constant-first-factor and unit normalization.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry.Etale

variable (Λ : Type (u + 1)) [CommRing Λ]
  {k : Type u} [Field k] [IsSepClosed k]

/-- (blueprint: definition-kunneth-map--1) The canonical tensor comparison for global sections
over a separably closed point. Source: Stacks Project, Tag 0F1E, read through the
constant-sheaf equivalence. It is the tensor comparison of the derived constant functor,
conjugated by its unit and counit and the exact-global-sections comparison.
-/
noncomputable def pointGlobalSectionsTensorIso
    (C D : DerivedCategory (Sheaf (Spec (.of k)).smallEtaleTopology
      (ModuleCat.{u + 1} Λ))) :
    (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) (Spec (.of k))).obj C ⊗
        (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) (Spec (.of k))).obj D ≅
      (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) (Spec (.of k))).obj
        (((derivedTensor (ModuleCat.{u + 1} Λ) (Spec (.of k))).obj C).obj D) :=
  let E := constantSheafEquivalenceOfIsSepClosed Λ (k := k)
  letI : E.functor.Additive := additive_constantSheaf Λ _
  letI : E.inverse.Additive := additive_sheafSections_obj Λ _
  let F := constantSheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ)
  letI : F.IsEquivalence := E.isEquivalence_functor
  let R := rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) (Spec (.of k))
  let e (T : DerivedCategory (Sheaf (Spec (.of k)).smallEtaleTopology
      (ModuleCat.{u + 1} Λ))) : F.mapDerivedCategory.obj (R.obj T) ≅ T :=
    F.mapDerivedCategory.mapIso ((rightDerivedGlobalSectionsIsoOfIsSepClosed Λ).app T) ≪≫
      E.mapDerivedCategory.counitIso.app T
  let e' (N : DerivedCategory (ModuleCat.{u + 1} Λ)) :
      R.obj (F.mapDerivedCategory.obj N) ≅ N :=
    (rightDerivedGlobalSectionsIsoOfIsSepClosed Λ).app _ ≪≫
      (E.mapDerivedCategory.unitIso.app N).symm
  let i : F.mapDerivedCategory.obj (R.obj C ⊗ R.obj D) ≅
      ((derivedTensor (ModuleCat.{u + 1} Λ) (Spec (.of k))).obj C).obj D :=
    mapDerivedCategoryObjTensorIsoDerivedTensor _ _ F (R.obj C) (R.obj D) ≪≫
      ((derivedTensor (ModuleCat.{u + 1} Λ) (Spec (.of k))).mapIso (e C)).app _ ≪≫
      ((derivedTensor (ModuleCat.{u + 1} Λ) (Spec (.of k))).obj C).mapIso (e D)
  (e' (R.obj C ⊗ R.obj D)).symm ≪≫ R.mapIso i

/-- (blueprint: definition-kunneth-map--1) The canonical external product in module-valued
global sections. Source: Stacks Project, Tag 0F1E, canonical adjoint construction.
First use the inverse Leray maps, then the canonical tensor comparison at the point,
then apply global sections to the existing adjunction mate `kunnethMap`, and finally
use Leray for the diagonal. No properness or boundedness is needed to define this map.
-/
noncomputable def kunnethGlobalSectionsMap
    {X Y Z : Scheme.{u}} (p : Z ⟶ X) (q : Z ⟶ Y)
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    (w : q ≫ g = p ≫ f)
    (E : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) X).obj E ⊗
        (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) Y).obj K ⟶
      (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) Z).obj
        (((derivedTensor (ModuleCat.{u + 1} Λ) Z).obj
          ((upperStar (ModuleCat.{u + 1} Λ) p).leftDerivedFunctor.obj E)).obj
          ((upperStar (ModuleCat.{u + 1} Λ) q).leftDerivedFunctor.obj K)) :=
  tensorHom
      ((rightDerivedLowerStarCompRightDerivedGlobalSectionsIso
        (ModuleCat.{u + 1} Λ) f).inv.app E)
      ((rightDerivedLowerStarCompRightDerivedGlobalSectionsIso
        (ModuleCat.{u + 1} Λ) g).inv.app K) ≫
    (pointGlobalSectionsTensorIso Λ _ _).hom ≫
    (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) (Spec (.of k))).map
      (kunnethMap (ModuleCat.{u + 1} Λ) p q f g (p ≫ f) rfl w E K) ≫
    (rightDerivedLowerStarCompRightDerivedGlobalSectionsIso
      (ModuleCat.{u + 1} Λ) (p ≫ f)).hom.app _

end AlgebraicGeometry.Etale
