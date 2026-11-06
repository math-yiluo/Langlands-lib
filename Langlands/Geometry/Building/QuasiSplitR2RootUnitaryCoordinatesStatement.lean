import Langlands.Geometry.Building.RootUnitaryCoordinateCompatibility
import Langlands.GroupScheme.Reductive.QuasiSplit

/-! # Actual quadratic unitary coordinates and the full centralizer action for type R2 roots -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme

namespace Langlands.Geometry.Building

/-- Every type R2 root of a quasi-split group has actual quadratic unitary
coordinates: a separable quadratic extension of finite separable extensions of
the base field parametrizing the actual rational root group, with the
zero-first-coordinate parameters giving the actual rational root group of the
double, and with the entire centralizer acting through an actual
extension-field character restricting to the root. No coordinates or
valuation data are supplied as hypotheses. -/
def QuasiSplitR2RootUnitaryCoordinatesStatement : Prop :=
  ∀ (k : Type u) [Field k]
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom],
    IsQuasiSplit G →
    ∀ (S : CommGroupScheme (Spec (CommRingCat.of k))) (i : S.toGrp ⟶ G),
      IsMaximalSplitTorus i →
      ∀ (Z : GroupScheme (Spec (CommRingCat.of k))) (j : Z ⟶ G),
        (torusCentralizer i).IsRepresentedBy j →
        ∀ (s : S.toGrp ⟶ Z), s ≫ j = i →
        ∀ a : characterLattice S,
          a ∈ relativeRoots i → 2 • a ∈ relativeRoots i →
            Nonempty (RootUnitaryCoordinates i j s a)

end Langlands.Geometry.Building
