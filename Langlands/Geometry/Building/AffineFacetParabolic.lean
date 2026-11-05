import Langlands.Geometry.Building.AffineIwahoriTits

/-!
# Actual facet stabilizers and generated parahorics

KP Proposition 7.5.5 as a fixed-data predicate. The facet-generated Weyl subgroup is
compared with the existing setwise affine facet stabilizer in the full Iwahori–Weyl group.
The generated full parahoric is compared with the standard parabolic of the same actual
Iwahori–Tits datum. These are assertions, not structural truth proofs.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme

namespace Langlands.Geometry.Building.ParahoricBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (P : ParahoricBuildingData G) [P.normalizerZero.Normal]

/-- The chamber-simple reflections whose defining affine roots vanish on the facet,
transported through the same comparison as the actual Tits system. -/
def facetSimpleInAffinePart
    (e : P.affinePart ≃* AffineRootSystem.affineWeylGroup P.affineRoots)
    (C Fa : Set P.Apartment) : Set P.affinePart :=
  e ⁻¹' AffineRootSystem.facetSimpleReflections P.affineRoots C Fa

theorem facetSimpleInAffinePart_subset
    (e : P.affinePart ≃* AffineRootSystem.affineWeylGroup P.affineRoots)
    (C Fa : Set P.Apartment) :
    P.facetSimpleInAffinePart e C Fa ⊆ P.chamberSimpleInAffinePart e C :=
  fun _ h => AffineRootSystem.facetSimpleReflections_subset P.affineRoots C Fa h

/-- The two comparisons of KP Proposition 7.5.5 for a facet of the chosen chamber.
The comparison `e` must be the one used in `AffineIwahoriTitsWith`, as retained by
`CommonChamberFacetParabolics`. -/
structure FacetParabolicComparisonWith (C Fa : Set P.Apartment)
    (e : P.affinePart ≃* AffineRootSystem.affineWeylGroup P.affineRoots) : Prop where
  face : AffineRootSystem.IsFaceOf P.affineRoots Fa C
  parahoric_le_zero : P.parahoric Fa ≤ P.zeroSubgroup
  weyl_stabilizer :
    (Subgroup.closure (P.facetSimpleInAffinePart e C Fa)).map P.affinePart.subtype =
      P.affineFacetStabilizer Fa
  parabolic_eq :
    (P.parahoricInZero Fa : Set P.zeroSubgroup) =
      Langlands.Group.TitsSystem.standardParabolic (P.parahoricInZero C)
        P.affineTitsProjection (P.facetSimpleInAffinePart e C Fa)

/-- Explicit subtype comparison with the generated full parahoric in `G(F)`. -/
theorem FacetParabolicComparisonWith.parahoric_image {C Fa : Set P.Apartment}
    {e : P.affinePart ≃* AffineRootSystem.affineWeylGroup P.affineRoots}
    (h : P.FacetParabolicComparisonWith C Fa e) :
    (P.parahoricInZero Fa).map P.zeroSubgroup.subtype = P.parahoric Fa :=
  P.parahoricInZero_map Fa h.parahoric_le_zero

/-- The union of the same Iwahori Bruhat cells, expressed in the full rational-point
group by its actual inclusion. No fixer or stabilizer is substituted for the parahoric. -/
theorem FacetParabolicComparisonWith.parahoric_eq_bruhat_cells
    {C Fa : Set P.Apartment}
    {e : P.affinePart ≃* AffineRootSystem.affineWeylGroup P.affineRoots}
    (h : P.FacetParabolicComparisonWith C Fa e) :
    (P.parahoric Fa : Set (rationalPoints G)) =
      P.zeroSubgroup.subtype ''
        Langlands.Group.TitsSystem.standardParabolic (P.parahoricInZero C)
          P.affineTitsProjection (P.facetSimpleInAffinePart e C Fa) := by
  rw [← h.parabolic_eq]
  change (P.parahoric Fa : Set (rationalPoints G)) =
    ((P.parahoricInZero Fa).map P.zeroSubgroup.subtype : Set (rationalPoints G))
  rw [h.parahoric_image]

/-- A single actual affine Iwahori–Tits datum and the two facet comparisons for a common
chamber, using one Weyl comparison, one Borel subgroup and one quotient projection. -/
def CommonChamberFacetParabolics (C F₁ F₂ : Set P.Apartment) : Prop :=
  ∃ e : P.affinePart ≃* AffineRootSystem.affineWeylGroup P.affineRoots,
    P.AffineIwahoriTitsWith C e ∧
      P.FacetParabolicComparisonWith C F₁ e ∧ P.FacetParabolicComparisonWith C F₂ e

end Langlands.Geometry.Building.ParahoricBuildingData
