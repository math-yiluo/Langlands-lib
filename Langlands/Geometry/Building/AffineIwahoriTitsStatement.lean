import Langlands.Geometry.Building.AffineIwahoriTits
import Langlands.Geometry.Building.KPApartmentAxioms

/-!
# The apartment-only affine Iwahori–Tits proof target

KP Theorem 7.5.3(1),(2), restricted to the `G(F)^0` branch. This is a proposition
definition, not a proof. Normality, containment, the actual-action comparison, the Tits
axioms and saturation are conclusions.
-/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme

namespace Langlands.Geometry.Building

/-- For every chamber, the actual `G(F)^0` Iwahori–Tits system exists under exactly
the apartment and chamber premises of `IwahoriDoubleCosetStatement`. -/
def AffineIwahoriTitsStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] (P : ParahoricBuildingData G),
    P.apartment.SatisfiesApartmentAxioms P.centralizer →
      ∀ C : Set P.Apartment, AffineRootSystem.IsChamber P.affineRoots C →
        ∃ (_ : P.normalizerZero.Normal) (_ : P.zeroSubgroup.Normal),
          P.AffineIwahoriTits C

end Langlands.Geometry.Building
