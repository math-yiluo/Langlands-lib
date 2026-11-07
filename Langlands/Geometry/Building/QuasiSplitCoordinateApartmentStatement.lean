import Langlands.Geometry.Building.RootUnitaryCoordinateCompatibility
import Langlands.Geometry.Building.IntegerValuationBuildingData
import Langlands.GroupScheme.Reductive.QuasiSplit
import Mathlib.RingTheory.Henselian

/-! # Actual quasi-split apartments with root coordinates for every centralizer datum -/

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme

namespace Langlands.Geometry.Building

/-- For every prescribed maximal split torus of a quasi-split group over a
henselian field with a surjective integer-valued valuation, and for every
actual centralizer datum of that torus, there is an actual normalizer-stable
equipollence class of root-datum valuations with a member `φ` described on
each relative root group through actual coordinates for the centralizer: an
equivariant coordinate family, or quadratic unitary coordinates on which `φ`
is the tower depth, or (for the double of a multipliable root) quadratic
unitary coordinates of the halved root on whose zero-first-coordinate
parameters `φ` is the central tower depth. -/
def QuasiSplitCoordinateApartmentStatement : Prop :=
  ∀ (k : Type u) [Field k]
    (v : Valuation k (WithZero (Multiplicative ℤ))),
    Function.Surjective v →
    ∀ hH : HenselianLocalRing v.valuationSubring,
    ∀ (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom],
      IsQuasiSplit G →
      ∀ (S : CommGroupScheme (Spec (CommRingCat.of k)))
        (i : S.toGrp ⟶ G) (hi : IsMaximalSplitTorus i),
        letI := mono_of_isMaximalSplitTorus hi
        ∀ C : CentralizerDatum i,
          ∃ (D : KPApartmentData i (IntegerValuation.order v))
            (φ : RootFunctionFamily S G), φ ∈ D.carrier ∧
            ∀ a ∈ relativeRoots i,
              Nonempty (IntegerValuation.RootCoordinateFamilyEquivariance v i C.j C.s φ a) ∨
              (∃ R : RootUnitaryCoordinates i C.j C.s a,
                ∀ p, φ a (R.equiv p) =
                  SU3Root.towerDepth k R.base R.extension v hH p) ∨
              ∃ b, 2 • b = a ∧ ∃ R : RootUnitaryCoordinates i C.j C.s b,
                ∀ q : SU3Root.Parameters.central
                    (SU3Root.fieldInvolution R.base R.extension),
                  φ a (R.equiv q.val) =
                    SU3Root.towerCentralDepth k R.base R.extension v hH q

end Langlands.Geometry.Building
