import Langlands.Geometry.Building.CentralizerCoordinateCompatibility
import Langlands.Geometry.Building.QuasiSplitR1RootFieldCoordinatesStatement

/-! # Full V6 from actual root field coordinates

Actual field coordinates `e : E ≃ U_a(k)` on which the centralizer acts through a character `β`
of `Z_E` restricting to `a` (`RootFieldCoordinates`) give equivariant coordinate data for every
norm-calibrated valuation `w` of `E`, provided the root function is `φ_a(e(x)) = w(x)`. Over a
henselian base the induced valuation of the finite separable extension `E` is norm-calibrated, so
such coordinates on every relative root give the integer centralizer compatibility V 6.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.BruhatTits

namespace Langlands.Geometry.Building

variable {k : Type u} [Field k]
  {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G Z : GroupScheme (Spec (CommRingCat.of k))}
  {i : S.toGrp ⟶ G} {j : Z ⟶ G} {s : S.toGrp ⟶ Z} {a : characterLattice S}

/-- Conjugation by the inverse of a centralizer point scales field coordinates by the inverse
character value. -/
theorem RootFieldCoordinates.conj_inv (R : RootFieldCoordinates i j s a)
    (z : rationalPoints Z) (x : R.extension) :
    (rationalPoints.map j z)⁻¹ * (R.equiv (Multiplicative.ofAdd x) : rationalPoints G) *
        rationalPoints.map j z =
      (R.equiv (Multiplicative.ofAdd
        ((((rationalCharacterEval R.character
          (GaloisPointComparison.rationalExtend k R.extension Z z))⁻¹ : R.extensionˣ) :
            R.extension) * x)) : rationalPoints G) := by
  have h := R.conjugation z⁻¹ x
  rwa [map_inv, inv_inv, map_inv, map_inv] at h

variable {v : Valuation k (WithZero (Multiplicative ℤ))}

open IntegerValuation in
/-- Equivariant coordinate data from actual root field coordinates, for a norm-calibrated
valuation `w` of the coordinate field and a root function with `φ_a(e(x)) = w(x)`. -/
def RootFieldCoordinates.toRootCoordinateEquivariance (R : RootFieldCoordinates i j s a)
    {w : AddValuation R.extension (WithTop ℝ)} (hw : IsNormCalibrated v w)
    {φ : RootFunctionFamily S G} (hφ : ∀ x : R.extension, φ a (R.equiv (Multiplicative.ofAdd x)) = w x) :
    RootCoordinateEquivariance v i j s φ a :=
  RootCoordinateEquivariance.ofMulEquiv hw R.equiv R.character R.restriction hφ R.conj_inv

variable (hH : HenselianLocalRing v.valuationSubring)

/-- Over a henselian base, equivariant coordinate data from actual root field coordinates and the
induced valuation of their finite separable coordinate field. -/
def RootFieldCoordinates.toRootCoordinateEquivarianceHenselian
    (R : RootFieldCoordinates i j s a) {φ : RootFunctionFamily S G}
    (hφ : ∀ x : R.extension, φ a (R.equiv (Multiplicative.ofAdd x)) =
      FieldTheory.henselianSeparableAddValuation v hH R.extension x) :
    IntegerValuation.RootCoordinateEquivariance v i j s φ a :=
  R.toRootCoordinateEquivariance
    (IntegerValuation.isNormCalibrated_henselianSeparableAddValuation hH R.extension) hφ

namespace IntegerValuation

/-- **Full V 6 from root field coordinates.** Over a henselian base, if every relative root group
has actual field coordinates on which `φ` is the induced valuation of the coordinate field, then
`φ` satisfies the integer centralizer compatibility. -/
theorem isCentralizerCompatible_of_rootFieldCoordinates [IsAffineHom G.X.hom]
    [IsAffine S.toGrp.X.left] [Mono i.hom.hom.left] [IsAffine Z.X.left]
    (hj : (torusCentralizer i).IsRepresentedBy j)
    (h : Function.Bijective (Cartan.restrictionEvaluation s)) {φ : RootFunctionFamily S G}
    (hc : ∀ a ∈ relativeRoots i, ∃ R : RootFieldCoordinates i j s a,
      ∀ x : R.extension, φ a (R.equiv (Multiplicative.ofAdd x)) =
        FieldTheory.henselianSeparableAddValuation v hH R.extension x) :
    IsCentralizerCompatible v i j s h φ :=
  isCentralizerCompatible_of_rootCoordinates hj h fun a ha =>
    let ⟨R, hR⟩ := hc a ha
    ⟨R.toRootCoordinateEquivarianceHenselian hH hR⟩

/-- **Omega compatibility from root field coordinates.** Over a henselian base, if one member of
the apartment class is, on every relative root group, the induced valuation of actual field
coordinates for the actual centralizer, then the whole class is Omega-compatible. -/
theorem isOmegaCompatible_of_rootFieldCoordinates [IsAffineHom G.X.hom]
    [IsAffine S.toGrp.X.left] [Mono i.hom.hom.left] {D : KPApartmentData i (order v)}
    {C : CentralizerDatum i} {φ : RootFunctionFamily S G} (hφ : φ ∈ D.carrier)
    (hc : ∀ a ∈ relativeRoots i, ∃ R : RootFieldCoordinates i C.j C.s a,
      ∀ x : R.extension, φ a (R.equiv (Multiplicative.ofAdd x)) =
        FieldTheory.henselianSeparableAddValuation v hH R.extension x) :
    IsOmegaCompatible v D C :=
  isOmegaCompatible_of_rootCoordinates hφ fun a ha =>
    let ⟨R, hR⟩ := hc a ha
    ⟨R.toRootCoordinateEquivarianceHenselian hH hR⟩

end IntegerValuation

end Langlands.Geometry.Building
