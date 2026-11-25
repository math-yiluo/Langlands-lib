/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleResolutionSectionTransfer
public import Mathlib.CategoryTheory.Preadditive.Injective.Resolution
import WeilConjectures.AlgebraicGeometry.OpenRestrictionPullbackUnit
import WeilConjectures.AlgebraicGeometry.EtaleResolutionSectionCanonicalData
import WeilConjectures.AlgebraicGeometry.EtaleResolutionSectionHomologyNaturality

/-!
# Natural Ext identifications for resolution section complexes

Source: Stacks Project, Tag 0A50, proof, and localization in Tag 03F3.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace AlgebraicGeometry.Etale

/-- Single-section cohomology identifications compatible with whole-to-open restriction,
restriction between opens, and a prescribed augmentation-preserving direct-image lift.
This statement involves neither a biproduct nor a morphism of short complexes.
Source: Stacks Project, Tag 0A50, proof (resolution sections), Tag 03F3 (localization),
and steps 3 and 4 of lem-weil-pbc-etale-mayer-vietoris-section-comparison.
(blueprint: lem-weil-pbc-etale-resolution-section-homology)

Proof: For each injective resolution, compute Ext from the constant lifted integer sheaf
by the Hom complex. The constant-sheaf/sections adjunction and evaluation at 1 identify
this Hom complex with sections in each degree, compatibly with the differential. For an
open immersion, inverse image is localization restriction. It preserves injectives
because extension by zero is its exact left adjoint. Thus the restricted resolution is
an injective resolution, and the same construction identifies sections over the open
with its Ext cohomology. Choose these identifications for every open from this common
construction. The adjunction unit represents whole-to-open restriction. For inclusions
of opens, composing the localization comparisons gives the inverse upperStarComp in
openCohomologyRestriction, so cocycles and boundaries give the first four identities.
For the last two identities, adjoint the specified lift α to a chain map from g inverse
image of I to J. The degree-zero augmentation equation says it lifts the identity on
inverse-image coefficients. Applying inverse image to a Hom cocycle and precomposing
with the constant-sheaf comparison is the unit on its representing section. Compose
with this chain map: the resulting cocycle is the one defining cohomologyMap g. On an
open use the same calculation after localization. Naturality of the unit and the two
upperStarComp comparisons give exactly openCohomologyPullback, including its coefficient
transport. Hence all identifications have these identities simultaneously. Boundaries
are preserved by the chain maps, and homotopic comparison lifts give the same maps.
Degree zero is the kernel of the first differential. Empty opens have zero sections
and zero cohomology, and the construction still applies; no covering or torsion
assumption enters the argument. -/
theorem exists_resolutionSection_homology_comparison
    {X Y : Scheme.{u}} (g : Y ⟶ X)
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (I : InjectiveResolution G)
    (J : InjectiveResolution ((upperStar AddCommGrpCat.{u + 1} g).obj G))
    (α : I.cocomplex ⟶
      ((lowerStar AddCommGrpCat.{u + 1} g).mapHomologicalComplex (.up ℕ)).obj J.cocomplex)
    (hα : I.ι.f 0 ≫ α.f 0 =
      (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g).unit.app G ≫
        (lowerStar AddCommGrpCat.{u + 1} g).map (J.ι.f 0)) :
    ∃ eX : ∀ q : ℕ,
      (((etaleSectionFunctor (Scheme.Etale.mk (𝟙 X))).mapHomologicalComplex (.up ℕ)).obj
        I.cocomplex).homology q ≃+ Sheaf.H G q,
    ∃ eOX : ∀ (W : X.Opens) (q : ℕ),
      (((etaleSectionFunctor (Scheme.Etale.mk W.ι)).mapHomologicalComplex (.up ℕ)).obj
        I.cocomplex).homology q ≃+
          Sheaf.H ((upperStar AddCommGrpCat.{u + 1} W.ι).obj G) q,
    ∃ eY : ∀ q : ℕ,
      (((etaleSectionFunctor (Scheme.Etale.mk (𝟙 Y))).mapHomologicalComplex (.up ℕ)).obj
        J.cocomplex).homology q ≃+
          Sheaf.H ((upperStar AddCommGrpCat.{u + 1} g).obj G) q,
    ∃ eOY : ∀ (W : Y.Opens) (q : ℕ),
      (((etaleSectionFunctor (Scheme.Etale.mk W.ι)).mapHomologicalComplex (.up ℕ)).obj
        J.cocomplex).homology q ≃+
          Sheaf.H ((upperStar AddCommGrpCat.{u + 1} W.ι).obj
            ((upperStar AddCommGrpCat.{u + 1} g).obj G)) q,
    (∀ W q x, eOX W q (HomologicalComplex.homologyMap (etaleSectionMap
      (MorphismProperty.Over.homMk W.ι (Category.comp_id _) :
        Scheme.Etale.mk W.ι ⟶ Scheme.Etale.mk (𝟙 X)) I.cocomplex) q x) =
      cohomologyMap W.ι G q (eX q x)) ∧
    (∀ (A B : X.Opens) (h : A ≤ B) q x,
      eOX A q (HomologicalComplex.homologyMap (etaleSectionMap
        (MorphismProperty.Over.homMk (X.homOfLE h) (X.homOfLE_ι _) :
          Scheme.Etale.mk A.ι ⟶ Scheme.Etale.mk B.ι) I.cocomplex) q x) =
        openCohomologyRestriction h G q (eOX B q x)) ∧
    (∀ W q x, eOY W q (HomologicalComplex.homologyMap (etaleSectionMap
      (MorphismProperty.Over.homMk W.ι (Category.comp_id _) :
        Scheme.Etale.mk W.ι ⟶ Scheme.Etale.mk (𝟙 Y)) J.cocomplex) q x) =
      cohomologyMap W.ι ((upperStar AddCommGrpCat.{u + 1} g).obj G) q (eY q x)) ∧
    (∀ (A B : Y.Opens) (h : A ≤ B) q x,
      eOY A q (HomologicalComplex.homologyMap (etaleSectionMap
        (MorphismProperty.Over.homMk (Y.homOfLE h) (Y.homOfLE_ι _) :
          Scheme.Etale.mk A.ι ⟶ Scheme.Etale.mk B.ι) J.cocomplex) q x) =
        openCohomologyRestriction h ((upperStar AddCommGrpCat.{u + 1} g).obj G) q
          (eOY B q x)) ∧
    (∀ q x, eY q (HomologicalComplex.homologyMap
      (globalResolutionSectionTransfer g I.cocomplex J.cocomplex α) q x) =
      cohomologyMap g G q (eX q x)) ∧
    (∀ W q x, eOY (g ⁻¹ᵁ W) q (HomologicalComplex.homologyMap
      (openResolutionSectionTransfer g I.cocomplex J.cocomplex α W) q x) =
      openCohomologyPullback g W G q (eOX W q x)) := by
  obtain ⟨cX⟩ := exists_resolutionSection_canonical_comparison G I
  obtain ⟨cY⟩ := exists_resolutionSection_canonical_comparison
    ((upperStar AddCommGrpCat.{u + 1} g).obj G) J
  refine ⟨cX.globalEquiv, cX.openEquiv, cY.globalEquiv, cY.openEquiv, ?_⟩
  exact resolutionSection_homology_naturality g G I J α hα cX cY

end AlgebraicGeometry.Etale
