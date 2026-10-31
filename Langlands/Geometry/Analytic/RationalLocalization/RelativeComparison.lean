import Langlands.Geometry.Analytic.RationalLocalization
import Langlands.Geometry.Analytic.GeneralizedAffinoid.StrictComparison
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RelativeSeriesComparison
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RelativeEquationComparison
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RelativeRationalComparison
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalPresentationEquivalence
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalExtension

/-! # Strict rational quotients as unit-radius relative rational quotients -/

noncomputable section

universe u

namespace Langlands.Analytic.RationalLocalization

open StrictTateAlgebra PresentedStrictAffinoidAlgebra

variable (K : Type u) [NormedField K] [IsUltrametricDist K]
  (P : PresentedStrictAffinoidAlgebra K)

/-- A unit-radius scalar series representing an actual element of `P`, obtained
by keeping the coefficients of a chosen strict Tate-series representative. -/
def scalarLift (a : P) :
    GeneralizedTateAlgebra (PresentedAffinoidAlgebra.ofStrict K P).polyradius K :=
  (GeneralizedTateAlgebra.unitAlgEquiv K).symm (representative K P a)

@[simp] theorem presentationMap_scalarLift (a : P) :
    PresentedAffinoidAlgebra.presentationMap K (PresentedAffinoidAlgebra.ofStrict K P)
        (scalarLift K P a) =
      (PresentedAffinoidAlgebra.strictEquiv K P).symm a := by
  have h := PresentedAffinoidAlgebra.strictAlgEquiv_symm_presentationMap K P
    (representative K P a)
  rw [presentationMap_representative] at h
  exact h.symm

variable [CompleteSpace K] (m : ℕ) (g : P) (n : Fin m → P)

/-- Bounded maps out of the actual strict rational quotient are determined by
the original coefficients and the fraction coordinates, with no unit-ideal
hypothesis. -/
theorem hom_ext_fractionCoordinate (B : Type*) [NormedCommRing B] [NormedAlgebra K B]
    (φ ψ : BoundedAlgHom K (algebra K P m g n) B)
    (hbase : ∀ a, φ (baseMap K P m g n a) = ψ (baseMap K P m g n a))
    (hfrac : ∀ j, φ (fractionCoordinate K P m g n j) = ψ (fractionCoordinate K P m g n j)) :
    φ = ψ := by
  apply RationalPresentation.hom_ext_base_coordinates K P.arity m P.ideal
    (seriesLift K P g) (fun j => seriesLift K P (n j)) B φ ψ
  · apply BoundedAlgHom.ext
    intro a
    have ha := hbase (modelEquiv K P a)
    change φ (RationalPresentation.baseMap K P.arity m P.ideal
        (seriesLift K P g) (fun j => seriesLift K P (n j))
          ((modelEquiv K P).symm (modelEquiv K P a))) =
      ψ (RationalPresentation.baseMap K P.arity m P.ideal
        (seriesLift K P g) (fun j => seriesLift K P (n j))
          ((modelEquiv K P).symm (modelEquiv K P a))) at ha
    simp only [BoundedAlgEquiv.symm_apply_apply] at ha
    exact ha
  · exact hfrac

/-- The unit-polyradius scalar rational quotient of the radius-one generalized
presentation of `P`, with scalar lifts of the actual denominator and numerators. -/
abbrev scalarAlgebra : PresentedAffinoidAlgebra K :=
  PresentedAffinoidAlgebra.RationalPresentation.algebra K
    (PresentedAffinoidAlgebra.ofStrict K P) (PositivePolyradius.unit (Fin m))
    (scalarLift K P g) (fun j => scalarLift K P (n j))

omit [CompleteSpace K] in
/-- The scalar fraction coordinates have norm at most one, hence uniformly
bounded monomials. -/
theorem scalarFraction_bounded :
    HasBoundedMonomials (Fin m) (scalarAlgebra K P m g n)
      (PresentedAffinoidAlgebra.RationalPresentation.fraction K
        (PresentedAffinoidAlgebra.ofStrict K P) (PositivePolyradius.unit (Fin m))
        (scalarLift K P g) (fun j => scalarLift K P (n j))) := by
  refine ⟨1, zero_lt_one, fun d => ?_⟩
  simpa only [PositivePolyradius.unit_weight] using
    GeneralizedTateAlgebra.monomialValue_norm_le_weight (PositivePolyradius.unit (Fin m))
      (scalarAlgebra K P m g n)
      (PresentedAffinoidAlgebra.norm_one_le K (scalarAlgebra K P m g n)) _
      (PresentedAffinoidAlgebra.RationalPresentation.norm_fraction_le K
        (PresentedAffinoidAlgebra.ofStrict K P) (PositivePolyradius.unit (Fin m))
        (scalarLift K P g) (fun j => scalarLift K P (n j))) d

omit [CompleteSpace K] in
/-- The scalar fractions solve the rational equations for the actual elements
transported by `strictEquiv⁻¹`. -/
theorem toScalar_equation (j : Fin m) :
    ((PresentedAffinoidAlgebra.RationalPresentation.baseMap K
      (PresentedAffinoidAlgebra.ofStrict K P) (PositivePolyradius.unit (Fin m))
      (scalarLift K P g) (fun j => scalarLift K P (n j))).comp
        (PresentedAffinoidAlgebra.strictEquiv K P).symm.toBoundedAlgHom) g *
      PresentedAffinoidAlgebra.RationalPresentation.fraction K
        (PresentedAffinoidAlgebra.ofStrict K P) (PositivePolyradius.unit (Fin m))
        (scalarLift K P g) (fun j => scalarLift K P (n j)) j =
    ((PresentedAffinoidAlgebra.RationalPresentation.baseMap K
      (PresentedAffinoidAlgebra.ofStrict K P) (PositivePolyradius.unit (Fin m))
      (scalarLift K P g) (fun j => scalarLift K P (n j))).comp
        (PresentedAffinoidAlgebra.strictEquiv K P).symm.toBoundedAlgHom) (n j) := by
  simpa only [BoundedAlgHom.comp_apply, BoundedAlgEquiv.toBoundedAlgHom_apply,
    presentationMap_scalarLift] using
    PresentedAffinoidAlgebra.RationalPresentation.fraction_equation K
      (PresentedAffinoidAlgebra.ofStrict K P) (PositivePolyradius.unit (Fin m))
      (scalarLift K P g) (fun j => scalarLift K P (n j)) j

/-- The forward bridge, by the bounded extension property of the actual strict
quotient: coefficients go through `strictEquiv⁻¹` and fractions to fractions. -/
def toScalar : BoundedAlgHom K (algebra K P m g n) (scalarAlgebra K P m g n) :=
  liftFromBase K P m g n (scalarAlgebra K P m g n)
    ((PresentedAffinoidAlgebra.RationalPresentation.baseMap K
      (PresentedAffinoidAlgebra.ofStrict K P) (PositivePolyradius.unit (Fin m))
      (scalarLift K P g) (fun j => scalarLift K P (n j))).comp
        (PresentedAffinoidAlgebra.strictEquiv K P).symm.toBoundedAlgHom)
    (PresentedAffinoidAlgebra.RationalPresentation.fraction K
      (PresentedAffinoidAlgebra.ofStrict K P) (PositivePolyradius.unit (Fin m))
      (scalarLift K P g) (fun j => scalarLift K P (n j)))
    (scalarFraction_bounded K P m g n) (toScalar_equation K P m g n)

theorem toScalar_baseMap (a : P) :
    toScalar K P m g n (baseMap K P m g n a) =
      PresentedAffinoidAlgebra.RationalPresentation.baseMap K
        (PresentedAffinoidAlgebra.ofStrict K P) (PositivePolyradius.unit (Fin m))
        (scalarLift K P g) (fun j => scalarLift K P (n j))
        ((PresentedAffinoidAlgebra.strictEquiv K P).symm a) :=
  congrArg (fun χ : BoundedAlgHom K P (scalarAlgebra K P m g n) => χ a)
    (liftFromBase_comp_baseMap K P m g n (scalarAlgebra K P m g n)
      ((PresentedAffinoidAlgebra.RationalPresentation.baseMap K
        (PresentedAffinoidAlgebra.ofStrict K P) (PositivePolyradius.unit (Fin m))
        (scalarLift K P g) (fun j => scalarLift K P (n j))).comp
          (PresentedAffinoidAlgebra.strictEquiv K P).symm.toBoundedAlgHom)
      (PresentedAffinoidAlgebra.RationalPresentation.fraction K
        (PresentedAffinoidAlgebra.ofStrict K P) (PositivePolyradius.unit (Fin m))
        (scalarLift K P g) (fun j => scalarLift K P (n j)))
      (scalarFraction_bounded K P m g n) (toScalar_equation K P m g n))

theorem toScalar_fractionCoordinate (j : Fin m) :
    toScalar K P m g n (fractionCoordinate K P m g n j) =
      PresentedAffinoidAlgebra.RationalPresentation.fraction K
        (PresentedAffinoidAlgebra.ofStrict K P) (PositivePolyradius.unit (Fin m))
        (scalarLift K P g) (fun j => scalarLift K P (n j)) j :=
  liftFromBase_fractionCoordinate K P m g n _ _ _ _ _ j

/-- The actual strict fraction coordinates solve the scalar rational equations
for the coefficient map transported by `strictEquiv`. -/
theorem ofScalar_equation (j : Fin m) :
    ((baseMap K P m g n).comp (PresentedAffinoidAlgebra.strictEquiv K P).toBoundedAlgHom)
        (PresentedAffinoidAlgebra.presentationMap K (PresentedAffinoidAlgebra.ofStrict K P)
          (scalarLift K P g)) * fractionCoordinate K P m g n j =
      ((baseMap K P m g n).comp (PresentedAffinoidAlgebra.strictEquiv K P).toBoundedAlgHom)
        (PresentedAffinoidAlgebra.presentationMap K (PresentedAffinoidAlgebra.ofStrict K P)
          (scalarLift K P (n j))) := by
  simpa only [BoundedAlgHom.comp_apply, BoundedAlgEquiv.toBoundedAlgHom_apply,
    presentationMap_scalarLift, BoundedAlgEquiv.apply_symm_apply] using
    coordinate_equation K P m g n j

/-- The strict fraction coordinates have the weighted monomial bound at unit radius. -/
theorem fractionCoordinate_bounded :
    GeneralizedTateAlgebra.HasBoundedMonomials (PositivePolyradius.unit (Fin m))
      (algebra K P m g n) (fractionCoordinate K P m g n) :=
  (GeneralizedTateAlgebra.hasBoundedMonomials_unit _ _).mpr
    (RationalPresentation.newCoordinates_bounded K P.arity m P.ideal
      (seriesLift K P g) (fun j => seriesLift K P (n j)))

/-- The backward bridge, by the bounded extension property of the weighted
scalar quotient: coefficients go through `strictEquiv` and fractions to the
actual strict fraction coordinates. -/
def ofScalar : BoundedAlgHom K (scalarAlgebra K P m g n) (algebra K P m g n) :=
  PresentedAffinoidAlgebra.RationalPresentation.liftFromBase K
    (PresentedAffinoidAlgebra.ofStrict K P) (PositivePolyradius.unit (Fin m))
    (scalarLift K P g) (fun j => scalarLift K P (n j)) (algebra K P m g n)
    ((baseMap K P m g n).comp (PresentedAffinoidAlgebra.strictEquiv K P).toBoundedAlgHom)
    (fractionCoordinate K P m g n) (fractionCoordinate_bounded K P m g n)
    (ofScalar_equation K P m g n)

theorem ofScalar_baseMap (a : PresentedAffinoidAlgebra.ofStrict K P) :
    ofScalar K P m g n
        (PresentedAffinoidAlgebra.RationalPresentation.baseMap K
          (PresentedAffinoidAlgebra.ofStrict K P) (PositivePolyradius.unit (Fin m))
          (scalarLift K P g) (fun j => scalarLift K P (n j)) a) =
      baseMap K P m g n (PresentedAffinoidAlgebra.strictEquiv K P a) :=
  congrArg (fun χ : BoundedAlgHom K (PresentedAffinoidAlgebra.ofStrict K P)
      (algebra K P m g n) => χ a)
    (PresentedAffinoidAlgebra.RationalPresentation.liftFromBase_comp_baseMap K
      (PresentedAffinoidAlgebra.ofStrict K P) (PositivePolyradius.unit (Fin m))
      (scalarLift K P g) (fun j => scalarLift K P (n j)) (algebra K P m g n)
      ((baseMap K P m g n).comp (PresentedAffinoidAlgebra.strictEquiv K P).toBoundedAlgHom)
      (fractionCoordinate K P m g n) (fractionCoordinate_bounded K P m g n)
      (ofScalar_equation K P m g n))

theorem ofScalar_fraction (j : Fin m) :
    ofScalar K P m g n
        (PresentedAffinoidAlgebra.RationalPresentation.fraction K
          (PresentedAffinoidAlgebra.ofStrict K P) (PositivePolyradius.unit (Fin m))
          (scalarLift K P g) (fun j => scalarLift K P (n j)) j) =
      fractionCoordinate K P m g n j :=
  PresentedAffinoidAlgebra.RationalPresentation.liftFromBase_fraction K
    (PresentedAffinoidAlgebra.ofStrict K P) (PositivePolyradius.unit (Fin m))
    (scalarLift K P g) (fun j => scalarLift K P (n j)) _ _ _ _ _ j

theorem ofScalar_toScalar (x : algebra K P m g n) :
    ofScalar K P m g n (toScalar K P m g n x) = x := by
  have h : (ofScalar K P m g n).comp (toScalar K P m g n) =
      BoundedAlgHom.id K (algebra K P m g n) := by
    apply hom_ext_fractionCoordinate K P m g n
    · intro a
      rw [BoundedAlgHom.comp_apply, toScalar_baseMap, ofScalar_baseMap,
        BoundedAlgEquiv.apply_symm_apply, BoundedAlgHom.id_apply]
    · intro j
      rw [BoundedAlgHom.comp_apply, toScalar_fractionCoordinate, ofScalar_fraction,
        BoundedAlgHom.id_apply]
  exact congrArg (fun χ => χ x) h

theorem toScalar_ofScalar (x : scalarAlgebra K P m g n) :
    toScalar K P m g n (ofScalar K P m g n x) = x := by
  have h : (toScalar K P m g n).comp (ofScalar K P m g n) =
      BoundedAlgHom.id K (scalarAlgebra K P m g n) := by
    apply PresentedAffinoidAlgebra.RationalPresentation.hom_ext K
      (PresentedAffinoidAlgebra.ofStrict K P) (PositivePolyradius.unit (Fin m))
      (scalarLift K P g) (fun j => scalarLift K P (n j))
    · intro a
      rw [BoundedAlgHom.comp_apply, ofScalar_baseMap, toScalar_baseMap,
        BoundedAlgEquiv.symm_apply_apply, BoundedAlgHom.id_apply]
    · intro j
      rw [BoundedAlgHom.comp_apply, ofScalar_fraction, toScalar_fractionCoordinate,
        BoundedAlgHom.id_apply]
  exact congrArg (fun χ => χ x) h

/-- The constructed bounded equivalence between the actual strict rational
quotient and the unit-polyradius scalar rational quotient of `ofStrict K P`. -/
def scalarEquiv : BoundedAlgEquiv K (algebra K P m g n) (scalarAlgebra K P m g n) :=
  BoundedAlgEquiv.ofHomInv (toScalar K P m g n) (ofScalar K P m g n)
    (ofScalar_toScalar K P m g n) (toScalar_ofScalar K P m g n)

@[simp] theorem scalarEquiv_baseMap (a : P) :
    scalarEquiv K P m g n (baseMap K P m g n a) =
      PresentedAffinoidAlgebra.RationalPresentation.baseMap K
        (PresentedAffinoidAlgebra.ofStrict K P) (PositivePolyradius.unit (Fin m))
        (scalarLift K P g) (fun j => scalarLift K P (n j))
        ((PresentedAffinoidAlgebra.strictEquiv K P).symm a) :=
  toScalar_baseMap K P m g n a

@[simp] theorem scalarEquiv_fractionCoordinate (j : Fin m) :
    scalarEquiv K P m g n (fractionCoordinate K P m g n j) =
      PresentedAffinoidAlgebra.RationalPresentation.fraction K
        (PresentedAffinoidAlgebra.ofStrict K P) (PositivePolyradius.unit (Fin m))
        (scalarLift K P g) (fun j => scalarLift K P (n j)) j :=
  toScalar_fractionCoordinate K P m g n j

@[simp] theorem scalarEquiv_symm_baseMap (a : PresentedAffinoidAlgebra.ofStrict K P) :
    (scalarEquiv K P m g n).symm
        (PresentedAffinoidAlgebra.RationalPresentation.baseMap K
          (PresentedAffinoidAlgebra.ofStrict K P) (PositivePolyradius.unit (Fin m))
          (scalarLift K P g) (fun j => scalarLift K P (n j)) a) =
      baseMap K P m g n (PresentedAffinoidAlgebra.strictEquiv K P a) :=
  ofScalar_baseMap K P m g n a

@[simp] theorem scalarEquiv_symm_fraction (j : Fin m) :
    (scalarEquiv K P m g n).symm
        (PresentedAffinoidAlgebra.RationalPresentation.fraction K
          (PresentedAffinoidAlgebra.ofStrict K P) (PositivePolyradius.unit (Fin m))
          (scalarLift K P g) (fun j => scalarLift K P (n j)) j) =
      fractionCoordinate K P m g n j :=
  ofScalar_fraction K P m g n j

/-- The actual strict rational quotient is boundedly equivalent to the
intrinsic relative rational quotient of `ofStrict K P` at unit radius, with
denominator `strictEquiv⁻¹ g` and numerators `strictEquiv⁻¹ (n j)`. -/
def relativeEquiv :
    BoundedAlgEquiv K (algebra K P m g n)
      (PresentedAffinoidAlgebra.RelativeRationalPresentation.Algebra K
        (PresentedAffinoidAlgebra.ofStrict K P) (PositivePolyradius.unit (Fin m))
        ((PresentedAffinoidAlgebra.strictEquiv K P).symm g)
        (fun j => (PresentedAffinoidAlgebra.strictEquiv K P).symm (n j))) :=
  ((scalarEquiv K P m g n).trans
    (PresentedAffinoidAlgebra.RationalPresentation.relativeEquiv K
      (PresentedAffinoidAlgebra.ofStrict K P) (PositivePolyradius.unit (Fin m))
      (scalarLift K P g) (fun j => scalarLift K P (n j)))).trans
    (PresentedAffinoidAlgebra.RationalPresentation.dataEquiv K _ _ _ _ _ _ (presentationMap_scalarLift K P g)
      (funext fun j => presentationMap_scalarLift K P (n j)))

/-- On original coefficients the comparison is `strictEquiv⁻¹` followed by the
relative coefficient map. -/
@[simp] theorem relativeEquiv_baseMap (a : P) :
    relativeEquiv K P m g n (baseMap K P m g n a) =
      PresentedAffinoidAlgebra.RelativeRationalPresentation.baseMap K
        (PresentedAffinoidAlgebra.ofStrict K P) (PositivePolyradius.unit (Fin m))
        ((PresentedAffinoidAlgebra.strictEquiv K P).symm g)
        (fun j => (PresentedAffinoidAlgebra.strictEquiv K P).symm (n j))
        ((PresentedAffinoidAlgebra.strictEquiv K P).symm a) := by
  change PresentedAffinoidAlgebra.RationalPresentation.dataEquiv K _ _ _ _ _ _ _ _
      (PresentedAffinoidAlgebra.RationalPresentation.relativeEquiv K
        (PresentedAffinoidAlgebra.ofStrict K P) (PositivePolyradius.unit (Fin m))
        (scalarLift K P g) (fun j => scalarLift K P (n j))
        (scalarEquiv K P m g n (baseMap K P m g n a))) = _
  rw [scalarEquiv_baseMap, PresentedAffinoidAlgebra.RationalPresentation.relativeEquiv_baseMap,
    PresentedAffinoidAlgebra.RationalPresentation.dataEquiv_baseMap]

/-- The comparison sends each strict fraction coordinate to the relative fraction. -/
@[simp] theorem relativeEquiv_fractionCoordinate (j : Fin m) :
    relativeEquiv K P m g n (fractionCoordinate K P m g n j) =
      PresentedAffinoidAlgebra.RelativeRationalPresentation.fraction K
        (PresentedAffinoidAlgebra.ofStrict K P) (PositivePolyradius.unit (Fin m))
        ((PresentedAffinoidAlgebra.strictEquiv K P).symm g)
        (fun j => (PresentedAffinoidAlgebra.strictEquiv K P).symm (n j)) j := by
  change PresentedAffinoidAlgebra.RationalPresentation.dataEquiv K _ _ _ _ _ _ _ _
      (PresentedAffinoidAlgebra.RationalPresentation.relativeEquiv K
        (PresentedAffinoidAlgebra.ofStrict K P) (PositivePolyradius.unit (Fin m))
        (scalarLift K P g) (fun j => scalarLift K P (n j))
        (scalarEquiv K P m g n (fractionCoordinate K P m g n j))) = _
  rw [scalarEquiv_fractionCoordinate,
    PresentedAffinoidAlgebra.RationalPresentation.relativeEquiv_fraction,
    PresentedAffinoidAlgebra.RationalPresentation.dataEquiv_fraction]

@[simp] theorem relativeEquiv_symm_baseMap (a : PresentedAffinoidAlgebra.ofStrict K P) :
    (relativeEquiv K P m g n).symm
        (PresentedAffinoidAlgebra.RelativeRationalPresentation.baseMap K
          (PresentedAffinoidAlgebra.ofStrict K P) (PositivePolyradius.unit (Fin m))
          ((PresentedAffinoidAlgebra.strictEquiv K P).symm g)
          (fun j => (PresentedAffinoidAlgebra.strictEquiv K P).symm (n j)) a) =
      baseMap K P m g n (PresentedAffinoidAlgebra.strictEquiv K P a) := by
  have h := relativeEquiv_baseMap K P m g n (PresentedAffinoidAlgebra.strictEquiv K P a)
  rw [BoundedAlgEquiv.symm_apply_apply] at h
  rw [← h, BoundedAlgEquiv.symm_apply_apply]

@[simp] theorem relativeEquiv_symm_fraction (j : Fin m) :
    (relativeEquiv K P m g n).symm
        (PresentedAffinoidAlgebra.RelativeRationalPresentation.fraction K
          (PresentedAffinoidAlgebra.ofStrict K P) (PositivePolyradius.unit (Fin m))
          ((PresentedAffinoidAlgebra.strictEquiv K P).symm g)
          (fun j => (PresentedAffinoidAlgebra.strictEquiv K P).symm (n j)) j) =
      fractionCoordinate K P m g n j := by
  rw [← relativeEquiv_fractionCoordinate, BoundedAlgEquiv.symm_apply_apply]

end Langlands.Analytic.RationalLocalization
