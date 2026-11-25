/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteCompactScalar.FiniteCompactScalarCoordinates
public import WeilConjectures.AlgebraicGeometry.Etale.ProEtale.EtaleProEtaleScalarMateData
import all WeilConjectures.AlgebraicGeometry.Sp.SpDirectImageEtaleMate

/-! # Bounded-below and ambient proper site comparisons -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Scheme.FiniteCompactScalar

/-- The included D+ site mate is the ambient counit mate, with the prescribed
intrinsic-realization identifications. This equality contains no change of coefficients.

Source: Stacks Tag 099R; `lem-finite-proper-scalar-transport`, Step 3.
(blueprint: lem-finite-proper-site-ambient-normalization).

Proof: the ambient geometric adjunction restricts to the D+ adjunction under
the exact-functor and right-derived inclusion comparisons. Include the counit
equation fixedComparisonDirectImageMatePlus_counit in the unbounded category.
The pullback comparison includes to the exact derived comparison square.
Naturality of that square and of the inclusion comparisons gives the ambient
counit equation. Injectivity of geometric adjunction transposition identifies
the included mate with directImageComparisonAmbient. Apply intrinsic realization
and compose with intrinsicSiteFunctorIso and the normalized direct-image
realization comparison. These are exactly the factors defining properSiteIso.
No choice of a new comparison is made. This argument includes zero coefficients,
empty schemes, and every lower bound. -/
theorem properSiteIso_hom_ambient
    (A : Type u) [CommRing A] [Finite A]
    {Z Y : Scheme.{u}} (g : Z ⟶ Y) [QuasiCompact g] [QuasiSeparated g]
    (H : DerivedCategory.Plus
      (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))) :
    (properSiteIso A g H).hom =
      (intrinsicSiteFunctorIso A Y).hom.app _ ≫
        (sfIntrinsicDerivedEquivalence Y A).functor.map
          ((ProEtale.directImageComparisonAmbient (ULift.{u + 1, u} A) g).app H.obj) ≫
        (sfIntrinsicDerivedDirectImageComparison g A).inv.app
          ((ProEtale.comparisonUpperStar
            (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) Z).mapDerivedCategory.obj H.obj) ≫
        (proEtaleConstantDerivedDirectImage g A).map
          ((intrinsicSiteFunctorIso A Z).inv.app H.obj) := by
  have h := ProEtale.sp_comparison_hom (ULift.{u + 1, u} A) g H.obj H.property
  have hh : (ProEtale.spDirectImageComparisonIso
      (ULift.{u + 1, u} A) g H.obj H.property).hom =
      (ProEtale.directImageComparisonAmbient (ULift.{u + 1, u} A) g).app H.obj := by
    simpa only [ProEtale.BoundaryComparison.directImageMate,
      ProEtale.BoundaryComparison.pullbackSquare, ProEtale.directImageComparisonAmbient,
      ProEtale.directImageComparisonAmbientPullbackIso,
      ProEtale.leftDerivedUpperStarIsoMapDerivedCategory,
      Etale.leftDerivedUpperStarIsoMapDerivedCategory,
      ProEtale.BoundaryComparison.comparison, TwoSquare.mk] using h
  have hhh := congrArg (fun t ↦ (intrinsicSiteFunctorIso A Y).hom.app _ ≫
    (sfIntrinsicDerivedEquivalence Y A).functor.map t ≫
      (sfIntrinsicDerivedDirectImageComparison g A).inv.app
        ((ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) Z).mapDerivedCategory.obj H.obj) ≫
      (proEtaleConstantDerivedDirectImage g A).map
        ((intrinsicSiteFunctorIso A Z).inv.app H.obj)) hh
  simpa only [properSiteIso, ProEtale.spDirectImageComparisonIso,
    Iso.trans_hom, Functor.mapIso_hom, Functor.map_comp, Iso.app_hom, Iso.symm_hom,
    Iso.app_inv, Etale.rightDerivedLowerStarPlus, Category.assoc] using hhh

end AlgebraicGeometry.Scheme.FiniteCompactScalar
