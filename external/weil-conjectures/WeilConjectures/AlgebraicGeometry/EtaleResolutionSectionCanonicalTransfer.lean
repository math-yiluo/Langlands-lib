/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleResolutionSectionCanonicalComparison
import WeilConjectures.AlgebraicGeometry.EtaleResolutionSectionCanonicalGlobalTransfer
import WeilConjectures.AlgebraicGeometry.EtaleResolutionSectionCanonicalOpenTransfer

/-!
# Transfer of normalized resolution comparisons

Source: Stacks Project, Tags 0A50 and 03F3.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace AlgebraicGeometry.Etale

/-- Canonical comparisons identify augmentation-preserving section transfers with pullback.
Source: Stacks Project, Tag 01F8 and Remark 01FB (functoriality through resolutions),
Tag 03F3 (localization), and Tag 0A50 (section complexes).
(blueprint: lem-weil-pbc-etale-resolution-section-canonical-transfer)

Proof: Adjunction sends α to a chain map β from g inverse image of I to J.
 Exactness of inverse image makes the source a resolution of g inverse image
 of G, and hα says β preserves that augmentation. On a cycle represented by
 f from the constant integer sheaf, β after g inverse image of f, precomposed
 with the constant-sheaf comparison, represents the Ext pullback class.
 This follows either from the derived-category formula for extMk, where the
 augmentation equation cancels the two resolution isomorphisms, or from
 independence of comparison lifts up to homotopy. Evaluation at 1 identifies
 the corresponding section with α evaluated at the terminal object followed
 by restriction along `terminalSectionPullback g`, exactly the explicit
 global transfer. The normalization fields of cX and cY identify the two
 homology classes with these Ext classes, giving the first identity. On W,
 carry out the same calculation with the free sheaf representing W and its
 identity generator. Naturality of the unit and the upperStarComp
 isomorphisms gives the coefficient transport in `openCohomologyPullback`;
 its section map is α followed by restriction along `openSectionPullback`.
 Surjectivity of homologyπ extends the calculation from cycles to all classes.
 Boundaries remain boundaries under these chain maps. Degree zero, empty
 opens, zero sheaves, and identity morphisms require no extra hypothesis. -/
theorem resolutionSection_canonical_transfer
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
      ((upperStar AddCommGrpCat.{u + 1} g).obj G) J) :
    (∀ q x, cY.globalEquiv q (HomologicalComplex.homologyMap
      (globalResolutionSectionTransfer g I.cocomplex J.cocomplex α) q x) =
      cohomologyMap g G q (cX.globalEquiv q x)) ∧
    (∀ W q x, cY.openEquiv (g ⁻¹ᵁ W) q (HomologicalComplex.homologyMap
      (openResolutionSectionTransfer g I.cocomplex J.cocomplex α W) q x) =
      openCohomologyPullback g W G q (cX.openEquiv W q x)) := by
  constructor
  · exact resolutionSection_canonical_transfer_global_pointwise g G I J α hα cX cY
  · exact resolutionSection_canonical_transfer_open g G I J α hα cX cY

end AlgebraicGeometry.Etale
