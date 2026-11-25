/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RestrictScalars
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusBaseChange
public import Mathlib.CategoryTheory.Adjunction.Unique
import WeilConjectures.AlgebraicGeometry.EtaleRestrictScalarsAcyclic

/-!
# Canonical coefficient comparisons for étale inverse and direct images

Source: Stacks Project, Tags 03FD and 0D6J(3); the inverse-image comparison uses
Mathlib's uniqueness of left adjoints and the sectionwise coextension adjunction.
(blueprint: lem-sbc-canonical-restrict-scalars-functor-comparisons)
-/

@[expose] public section

universe u

open CategoryTheory
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] (φ : Λ →+* Λ')
  {Z W : Scheme.{u}} (f : Z ⟶ W)

/-- Direct image and restriction of scalars commute sectionwise. 
(blueprint: lem-sbc-canonical-restrict-scalars-functor-comparisons)
-/
noncomputable def lowerStarRestrictScalarsIso :
    (f)_*[ModuleCat.{u + 1} Λ'] ⋙ Sheaf.restrictScalars W.smallEtaleTopology φ ≅
      Sheaf.restrictScalars Z.smallEtaleTopology φ ⋙ (f)_*[ModuleCat.{u + 1} Λ] :=
  Iso.refl _

/-- Inverse image commutes with restriction of scalars: both composites are left
adjoint to the same sectionwise composite of direct image and coextension of scalars. 
(blueprint: lem-sbc-canonical-restrict-scalars-functor-comparisons)
-/
noncomputable def upperStarRestrictScalarsIsoSheaf :
    Sheaf.restrictScalars W.smallEtaleTopology φ ⋙ (f)^*[ModuleCat.{u + 1} Λ] ≅
      (f)^*[ModuleCat.{u + 1} Λ'] ⋙ Sheaf.restrictScalars Z.smallEtaleTopology φ :=
  Adjunction.leftAdjointUniq
    ((Sheaf.restrictCoextendScalarsAdj W.smallEtaleTopology φ).comp
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f))
    ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ') f).comp
      (Sheaf.restrictCoextendScalarsAdj Z.smallEtaleTopology φ))

/-- The inverse-image coefficient comparison on bounded below derived categories. 
(blueprint: lem-sbc-canonical-restrict-scalars-functor-comparisons)
-/
noncomputable def derivedUpperStarRestrictScalarsIso :
    (Sheaf.restrictScalars W.smallEtaleTopology φ).mapDerivedCategoryPlus ⋙
        D+((f)^*[ModuleCat.{u + 1} Λ]) ≅
      D+((f)^*[ModuleCat.{u + 1} Λ']) ⋙
        (Sheaf.restrictScalars Z.smallEtaleTopology φ).mapDerivedCategoryPlus :=
  (Functor.mapDerivedCategoryPlusCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryPlusNatIso (upperStarRestrictScalarsIsoSheaf φ f) ≪≫
    Functor.mapDerivedCategoryPlusCompIso _ _

/-- The canonical derived direct-image coefficient comparison, defined by the
universal property of the bounded below right derived functor. 
(blueprint: lem-sbc-canonical-restrict-scalars-functor-comparisons)
-/
noncomputable def derivedLowerStarRestrictScalarsMap :
    R+((f)_*[ModuleCat.{u + 1} Λ']) ⋙
        (Sheaf.restrictScalars W.smallEtaleTopology φ).mapDerivedCategoryPlus ⟶
      (Sheaf.restrictScalars Z.smallEtaleTopology φ).mapDerivedCategoryPlus ⋙
        R+((f)_*[ModuleCat.{u + 1} Λ]) :=
  Functor.rightDerivedFunctorPlusBaseChange (lowerStarRestrictScalarsIso φ f).hom

/-- The canonical derived direct-image comparison is invertible because restriction
sends injectives to direct-image acyclics.
Source: Stacks Project, Tag 0D6J(3), with the acyclicity argument of Tag 03FD.
Proof: apply the bounded-below derived comparison criterion to the sectionwise
identity on direct images and to restricted-injective direct-image acyclicity.
(blueprint: lem-sbc-canonical-restrict-scalars-functor-comparisons) -/
theorem isIso_derivedLowerStarRestrictScalarsMap :
    IsIso (derivedLowerStarRestrictScalarsMap φ f) := by
  exact Functor.isIso_rightDerivedFunctorPlusBaseChange_of_rightAcyclic
    (lowerStarRestrictScalarsIso φ f)
    (fun I ↦ rightAcyclic_lowerStar_restrictScalars_obj φ f I)

/-- The canonical derived direct-image coefficient isomorphism. 
(blueprint: lem-sbc-canonical-restrict-scalars-functor-comparisons)
-/
noncomputable def derivedLowerStarRestrictScalarsIso :
    R+((f)_*[ModuleCat.{u + 1} Λ']) ⋙
        (Sheaf.restrictScalars W.smallEtaleTopology φ).mapDerivedCategoryPlus ≅
      (Sheaf.restrictScalars Z.smallEtaleTopology φ).mapDerivedCategoryPlus ⋙
        R+((f)_*[ModuleCat.{u + 1} Λ]) := by
  have := isIso_derivedLowerStarRestrictScalarsMap φ f
  exact asIso (derivedLowerStarRestrictScalarsMap φ f)

variable {X S T Y : Scheme.{u}}

/-- The source comparison before taking homology, assembled from the inverse-image
comparison and the inverse of the canonical direct-image comparison. 
(blueprint: lem-sbc-canonical-restrict-scalars-functor-comparisons)
-/
noncomputable def derivedBaseChangeSourceRestrictScalarsIso (p : X ⟶ S) (g : T ⟶ S)
    (K : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ'))) :
    (D+((p)^*[ModuleCat.{u + 1} Λ])).obj
        ((R+((g)_*[ModuleCat.{u + 1} Λ])).obj
          ((Sheaf.restrictScalars T.smallEtaleTopology φ).mapDerivedCategoryPlus.obj K)) ≅
      (Sheaf.restrictScalars X.smallEtaleTopology φ).mapDerivedCategoryPlus.obj
        ((D+((p)^*[ModuleCat.{u + 1} Λ'])).obj
          ((R+((g)_*[ModuleCat.{u + 1} Λ'])).obj K)) :=
  (D+((p)^*[ModuleCat.{u + 1} Λ])).mapIso
      ((derivedLowerStarRestrictScalarsIso φ g).symm.app K) ≪≫
    (derivedUpperStarRestrictScalarsIso φ p).app
      ((R+((g)_*[ModuleCat.{u + 1} Λ'])).obj K)

/-- The target comparison before taking homology, assembled from the inverse-image
comparison followed by the inverse of the canonical direct-image comparison. 
(blueprint: lem-sbc-canonical-restrict-scalars-functor-comparisons)
-/
noncomputable def derivedBaseChangeTargetRestrictScalarsIso (e : Y ⟶ T) (h : Y ⟶ X)
    (K : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ'))) :
    (R+((h)_*[ModuleCat.{u + 1} Λ])).obj
        ((D+((e)^*[ModuleCat.{u + 1} Λ])).obj
          ((Sheaf.restrictScalars T.smallEtaleTopology φ).mapDerivedCategoryPlus.obj K)) ≅
      (Sheaf.restrictScalars X.smallEtaleTopology φ).mapDerivedCategoryPlus.obj
        ((R+((h)_*[ModuleCat.{u + 1} Λ'])).obj
          ((D+((e)^*[ModuleCat.{u + 1} Λ'])).obj K)) :=
  (R+((h)_*[ModuleCat.{u + 1} Λ])).mapIso
      ((derivedUpperStarRestrictScalarsIso φ e).app K) ≪≫
    (derivedLowerStarRestrictScalarsIso φ h).symm.app
      ((D+((e)^*[ModuleCat.{u + 1} Λ'])).obj K)

end AlgebraicGeometry.Etale
