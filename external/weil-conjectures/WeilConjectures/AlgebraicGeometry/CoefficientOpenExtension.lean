/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.CoefficientAffineConstructibleProEtaleModules
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Small

/-! # Extension by zero on coefficient-sized sites

Source: Stacks Project, Tags 03DI and 09AF.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits

-- The universe-polymorphic `hasSheafify_of_essentiallySmall` gets stuck on the universe of
-- `ModuleCat.{max v (u + 1)}`; Mathlib's concrete-category instance applies instead.
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

namespace AlgebraicGeometry.ProEtale

/-- Composition with an open immersion on the coefficient-sized pro-etale sites.
Source: Stacks Tags 03DI and 09AF (auxiliary; not a blueprint node). -/
abbrev coefficientOpenProEtaleMap {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] :
    Scheme.coefficientProEtaleSiteModel.{u, v} U ⥤
      Scheme.coefficientProEtaleSiteModel.{u, v} X :=
  AsSmall.down ⋙ MorphismProperty.Over.map ⊤
    (inferInstance : @WeaklyEtale _ _ j) ⋙ AsSmall.up

/-- Composition with an open immersion on the coefficient-sized etale sites.
Source: Stacks Tags 03DI and 09AF (auxiliary; not a blueprint node). -/
abbrev coefficientOpenEtaleMap {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] :
    Scheme.smallModelComparisonEtaleSite.{u, v} U ⥤
      Scheme.smallModelComparisonEtaleSite.{u, v} X :=
  AsSmall.down ⋙ MorphismProperty.Over.map ⊤
    (inferInstance : @Etale _ _ j) ⋙ AsSmall.up

instance coefficientOpenProEtaleMap_isContinuous {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] :
    (coefficientOpenProEtaleMap.{u, v} j).IsContinuous
      (Scheme.coefficientProEtaleModelTopology.{u, v} U)
      (Scheme.coefficientProEtaleModelTopology.{u, v} X) := by
  have : (AsSmall.up : X.ProEt ⥤ Scheme.coefficientProEtaleSiteModel.{u, v} X).IsContinuous
      (Scheme.ProEt.topology X) (Scheme.coefficientProEtaleModelTopology.{u, v} X) :=
    inferInstanceAs
      ((AsSmall.equiv.{u, u + 1, max v (u + 1)} (C := X.ProEt)).functor.IsContinuous
        (Scheme.ProEt.topology X)
        ((AsSmall.equiv.{u, u + 1, max v (u + 1)} (C := X.ProEt)).inverse.inducedTopology
          (Scheme.ProEt.topology X)))
  have := Functor.isContinuous_comp
    (MorphismProperty.Over.map ⊤ (inferInstance : @WeaklyEtale _ _ j))
    (AsSmall.up : X.ProEt ⥤ Scheme.coefficientProEtaleSiteModel.{u, v} X)
    (Scheme.ProEt.topology U) (Scheme.ProEt.topology X)
    (Scheme.coefficientProEtaleModelTopology.{u, v} X)
  exact Functor.isContinuous_comp AsSmall.down
    (MorphismProperty.Over.map ⊤ (inferInstance : @WeaklyEtale _ _ j) ⋙ AsSmall.up)
    (Scheme.coefficientProEtaleModelTopology.{u, v} U) (Scheme.ProEt.topology U)
    (Scheme.coefficientProEtaleModelTopology.{u, v} X)

instance coefficientOpenEtaleMap_isContinuous {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] :
    (coefficientOpenEtaleMap.{u, v} j).IsContinuous
      (Scheme.smallModelComparisonEtaleTopology.{u, v} U)
      (Scheme.smallModelComparisonEtaleTopology.{u, v} X) := by
  have : (AsSmall.up : X.Etale ⥤ Scheme.smallModelComparisonEtaleSite.{u, v} X).IsContinuous
      X.smallEtaleTopology (Scheme.smallModelComparisonEtaleTopology.{u, v} X) :=
    inferInstanceAs
      ((AsSmall.equiv.{u, u + 1, max v (u + 1)} (C := X.Etale)).functor.IsContinuous
        X.smallEtaleTopology
        ((AsSmall.equiv.{u, u + 1, max v (u + 1)} (C := X.Etale)).inverse.inducedTopology
          X.smallEtaleTopology))
  have : (MorphismProperty.Over.map ⊤ (inferInstance : @Etale _ _ j)).IsContinuous
      U.smallEtaleTopology X.smallEtaleTopology :=
    Scheme.isContinuous_overMap (P := @Etale) (Q := @Etale)
      (inferInstance : @Etale _ _ j) le_rfl
  have := Functor.isContinuous_comp
    (MorphismProperty.Over.map ⊤ (inferInstance : @Etale _ _ j))
    (AsSmall.up : X.Etale ⥤ Scheme.smallModelComparisonEtaleSite.{u, v} X)
    U.smallEtaleTopology X.smallEtaleTopology
    (Scheme.smallModelComparisonEtaleTopology.{u, v} X)
  exact Functor.isContinuous_comp AsSmall.down
    (MorphismProperty.Over.map ⊤ (inferInstance : @Etale _ _ j) ⋙ AsSmall.up)
    (Scheme.smallModelComparisonEtaleTopology.{u, v} U) U.smallEtaleTopology
    (Scheme.smallModelComparisonEtaleTopology.{u, v} X)

/-- Pro-etale open extension by zero: left Kan extension followed by sheafification.
Source: Stacks Tag 03DI (auxiliary; not a blueprint node). -/
def coefficientOpenProEtaleExtension (A : Type (max v (u + 1))) [CommRing A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :=
  Functor.sheafPullbackConstruction.sheafPullback
    (coefficientOpenProEtaleMap.{u, v} j) (ModuleCat.{max v (u + 1)} A)
    (Scheme.coefficientProEtaleModelTopology.{u, v} U)
    (Scheme.coefficientProEtaleModelTopology.{u, v} X)

/-- Etale open extension by zero: left Kan extension followed by sheafification.
Source: Stacks Tag 03DI (auxiliary; not a blueprint node). -/
def coefficientOpenEtaleExtension (A : Type (max v (u + 1))) [CommRing A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :=
  Functor.sheafPullbackConstruction.sheafPullback
    (coefficientOpenEtaleMap.{u, v} j) (ModuleCat.{max v (u + 1)} A)
    (Scheme.smallModelComparisonEtaleTopology.{u, v} U)
    (Scheme.smallModelComparisonEtaleTopology.{u, v} X)

/-- Comparison commutes with open extension by zero in the coefficient universe.
Source: Stacks Project, Tag 09AF (auxiliary; not a blueprint node).

The two right adjoints are restriction along equal composites of site functors.
Their identity natural isomorphism has a conjugate between the composite left
adjoints. All functors are constructed by Kan extension and sheafification. -/
def coefficientOpenExtensionComparisonIso (A : Type (max v (u + 1))) [CommRing A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    coefficientOpenEtaleExtension.{u, v} A j ⋙
      Functor.sheafPullbackConstruction.sheafPullback
        (Scheme.smallModelComparisonInclusion.{u, v} X) (ModuleCat.{max v (u + 1)} A)
        (Scheme.smallModelComparisonEtaleTopology.{u, v} X)
        (Scheme.coefficientProEtaleModelTopology.{u, v} X) ≅
    Functor.sheafPullbackConstruction.sheafPullback
        (Scheme.smallModelComparisonInclusion.{u, v} U) (ModuleCat.{max v (u + 1)} A)
        (Scheme.smallModelComparisonEtaleTopology.{u, v} U)
        (Scheme.coefficientProEtaleModelTopology.{u, v} U) ⋙
      coefficientOpenProEtaleExtension.{u, v} A j := by
  let ae := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (coefficientOpenEtaleMap.{u, v} j) (ModuleCat A)
    (Scheme.smallModelComparisonEtaleTopology U) (Scheme.smallModelComparisonEtaleTopology X)
  let ap := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (coefficientOpenProEtaleMap.{u, v} j) (ModuleCat A)
    (Scheme.coefficientProEtaleModelTopology U) (Scheme.coefficientProEtaleModelTopology X)
  let ax := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (Scheme.smallModelComparisonInclusion.{u, v} X) (ModuleCat A)
    (Scheme.smallModelComparisonEtaleTopology X) (Scheme.coefficientProEtaleModelTopology X)
  let au := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (Scheme.smallModelComparisonInclusion.{u, v} U) (ModuleCat A)
    (Scheme.smallModelComparisonEtaleTopology U) (Scheme.coefficientProEtaleModelTopology U)
  exact ((conjugateIsoEquiv (ae.comp ax) (au.comp ap)).symm (Iso.refl _)).symm

end AlgebraicGeometry.ProEtale
