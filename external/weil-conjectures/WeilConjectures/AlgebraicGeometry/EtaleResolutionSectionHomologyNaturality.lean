/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Preadditive.Injective.Resolution
public import WeilConjectures.AlgebraicGeometry.EtaleResolutionSectionTransfer
public import WeilConjectures.AlgebraicGeometry.EtaleResolutionSectionCanonicalComparison
import WeilConjectures.AlgebraicGeometry.EtaleResolutionSectionCanonicalRestriction
import WeilConjectures.AlgebraicGeometry.EtaleResolutionSectionCanonicalTransfer

/-!
# Naturality of normalized resolution section comparisons

Source: Stacks Project, Tags 0A50, 03F3, and 01F8.
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace AlgebraicGeometry.Etale

/-- Normalized section-homology equivalences satisfy the six compatibility families.
Source: Stacks Project, Tag 0A50 (resolution sections), Tag 03F3 (localization),
and Tag 01F8 (functoriality through resolutions).
(blueprint: lem-weil-pbc-etale-resolution-section-homology-naturality)

Arbitrary equivalences need not satisfy this compatibility:
independently negating one equivalence need not preserve a nonzero restriction map.
The corrected assertion requires the comparisons to have their canonical cocycle values.

Proof: Restriction naturality for cX supplies the first two identities on X and,
applied to cY, the next two on Y. Transfer naturality for these two normalized families
supplies the global and open transfer identities. Package the six identities. -/
theorem resolutionSection_homology_naturality
    {X Y : Scheme.{u}} (g : Y ⟶ X)
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (I : InjectiveResolution G)
    (J : InjectiveResolution ((upperStar AddCommGrpCat.{u + 1} g).obj G))
    (α : I.cocomplex ⟶
      ((lowerStar AddCommGrpCat.{u + 1} g).mapHomologicalComplex (.up ℕ)).obj J.cocomplex)
    (hα : I.ι.f 0 ≫ α.f 0 =
      (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g).unit.app G ≫
        (lowerStar AddCommGrpCat.{u + 1} g).map (J.ι.f 0))
    (cX : ResolutionSectionCanonicalComparison G I)
    (cY : ResolutionSectionCanonicalComparison
      ((upperStar AddCommGrpCat.{u + 1} g).obj G) J)
    : (∀ W q x, cX.openEquiv W q (HomologicalComplex.homologyMap (etaleSectionMap
      (MorphismProperty.Over.homMk W.ι (Category.comp_id _) :
        Scheme.Etale.mk W.ι ⟶ Scheme.Etale.mk (𝟙 X)) I.cocomplex) q x) =
      cohomologyMap W.ι G q (cX.globalEquiv q x)) ∧
    (∀ (A B : X.Opens) (h : A ≤ B) q x,
      cX.openEquiv A q (HomologicalComplex.homologyMap (etaleSectionMap
        (MorphismProperty.Over.homMk (X.homOfLE h) (X.homOfLE_ι _) :
          Scheme.Etale.mk A.ι ⟶ Scheme.Etale.mk B.ι) I.cocomplex) q x) =
        openCohomologyRestriction h G q (cX.openEquiv B q x)) ∧
    (∀ W q x, cY.openEquiv W q (HomologicalComplex.homologyMap (etaleSectionMap
      (MorphismProperty.Over.homMk W.ι (Category.comp_id _) :
        Scheme.Etale.mk W.ι ⟶ Scheme.Etale.mk (𝟙 Y)) J.cocomplex) q x) =
      cohomologyMap W.ι ((upperStar AddCommGrpCat.{u + 1} g).obj G) q (cY.globalEquiv q x)) ∧
    (∀ (A B : Y.Opens) (h : A ≤ B) q x,
      cY.openEquiv A q (HomologicalComplex.homologyMap (etaleSectionMap
        (MorphismProperty.Over.homMk (Y.homOfLE h) (Y.homOfLE_ι _) :
          Scheme.Etale.mk A.ι ⟶ Scheme.Etale.mk B.ι) J.cocomplex) q x) =
        openCohomologyRestriction h ((upperStar AddCommGrpCat.{u + 1} g).obj G) q
          (cY.openEquiv B q x)) ∧
    (∀ q x, cY.globalEquiv q (HomologicalComplex.homologyMap
      (globalResolutionSectionTransfer g I.cocomplex J.cocomplex α) q x) =
      cohomologyMap g G q (cX.globalEquiv q x)) ∧
    (∀ W q x, cY.openEquiv (g ⁻¹ᵁ W) q (HomologicalComplex.homologyMap
      (openResolutionSectionTransfer g I.cocomplex J.cocomplex α W) q x) =
      openCohomologyPullback g W G q (cX.openEquiv W q x)) := by
  obtain ⟨hX, hOX⟩ := resolutionSection_canonical_restriction G I cX
  obtain ⟨hY, hOY⟩ := resolutionSection_canonical_restriction
    ((upperStar AddCommGrpCat.{u + 1} g).obj G) J cY
  obtain ⟨hglobal, hopen⟩ := resolutionSection_canonical_transfer g G I J α hα cX cY
  exact ⟨hX, hOX, hY, hOY, hglobal, hopen⟩

end AlgebraicGeometry.Etale
