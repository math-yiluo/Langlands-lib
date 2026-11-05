import Langlands.Geometry.Building.AffineFacetParabolic
import Langlands.Geometry.Building.KPApartmentAxioms

/-!
# The apartment-only common-chamber facet-parabolic proof target

KP Proposition 7.5.5, packaged for the two facets of the unchanged parahoric
double-coset target. This proposition definition adds no global premise.
-/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme

namespace Langlands.Geometry.Building

/-- The two actual facet-parabolic comparisons share a single actual Iwahori–Tits
datum. The premises are exactly the apartment, chamber and common-chamber face premises
of `ParahoricDoubleCosetStatement`; normalities and all comparisons are conclusions. -/
def FacetParabolicComparisonStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] (P : ParahoricBuildingData G),
    P.apartment.SatisfiesApartmentAxioms P.centralizer →
      ∀ C F₁ F₂ : Set P.Apartment, AffineRootSystem.IsChamber P.affineRoots C →
        AffineRootSystem.IsFaceOf P.affineRoots F₁ C →
        AffineRootSystem.IsFaceOf P.affineRoots F₂ C →
        ∃ (_ : P.normalizerZero.Normal) (_ : P.zeroSubgroup.Normal),
          P.CommonChamberFacetParabolics C F₁ F₂

end Langlands.Geometry.Building
