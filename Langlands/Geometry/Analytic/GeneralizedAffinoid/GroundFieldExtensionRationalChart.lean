import Langlands.Geometry.Analytic.GeneralizedAffinoid.GroundFieldExtension
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalChartDomain
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalBaseChange
import Langlands.Geometry.Analytic.AtlasIntersectionFiniteRecognition

/-! # Ground field extension of rational charts -/

noncomputable section

universe u v

namespace Langlands.Analytic.PresentedAffinoidAlgebra.GroundFieldExtension

open GeneralizedTateAlgebra

section Chart

variable (K : Type u) [NormedField K] [IsUltrametricDist K]
  (L : Type v) [NormedField L] [IsUltrametricDist L] [NormedAlgebra K L]
  {A : PresentedAffinoidAlgebra K}

/-- The coefficient extension of a scalar weighted series of `A` to a weighted
series over `L` with the same polyradius. -/
abbrev extendSeries (h : GeneralizedTateAlgebra A.polyradius K) :
    GeneralizedTateAlgebra (algebra K L A).polyradius L :=
  mapCoefficientsAlgHom A.polyradius (coefficientMap K L) h

theorem presentationMap_extendSeries (h : GeneralizedTateAlgebra A.polyradius K) :
    presentationMap L (algebra K L A) (extendSeries K L h) =
      iota K L A (presentationMap K A h) := rfl

/-- The extended rational data still generate the unit ideal. -/
theorem generatesUnitIdeal_extend (d : RationalChart K A) :
    RationalPresentation.GeneratesUnitIdeal L (algebra K L A)
      (extendSeries K L d.denominator) (fun j => extendSeries K L (d.numerators j)) := by
  have h := congrArg (Ideal.map (iota K L A).toAlgHom.toRingHom) d.generates
  rw [Ideal.map_span, Ideal.map_top] at h
  unfold RationalPresentation.GeneratesUnitIdeal
  rw [← h, Set.image_insert_eq, ← Set.range_comp]
  rfl

/-- The ground field extension of a rational chart: the rational chart of `A_L`
with the same radii and the coefficient-extended denominator and numerators. -/
def rationalChart (d : RationalChart K A) : RationalChart L (algebra K L A) where
  arity := d.arity
  radii := d.radii
  denominator := extendSeries K L d.denominator
  numerators j := extendSeries K L (d.numerators j)
  generates := generatesUnitIdeal_extend K L d

@[simp] theorem arity_rationalChart (d : RationalChart K A) :
    (rationalChart K L d).arity = d.arity := rfl

/-- The locus of the extended chart is the preimage of the original locus. -/
theorem locus_rationalChart (d : RationalChart K A) :
    (rationalChart K L d).locus = spectrumProjection K L A ⁻¹' d.locus := rfl

end Chart

section Comparison

variable (K : Type u) [NormedField K] [IsUltrametricDist K]
  (L : Type v) [NormedField L] [IsUltrametricDist L] [NormedAlgebra K L]
  {A : PresentedAffinoidAlgebra K} (d : RationalChart K A)

/-- The fraction coordinates of `d`, typed in its chart algebra. -/
def chartFraction (j : Fin d.arity) : d.algebra :=
  RationalPresentation.fraction K A d.radii d.denominator d.numerators j

theorem chartFraction_equation (j : Fin d.arity) :
    d.baseMap (presentationMap K A d.denominator) * chartFraction K d j =
      d.baseMap (presentationMap K A (d.numerators j)) :=
  RationalPresentation.fraction_equation K A d.radii d.denominator d.numerators j

/-- The chart algebra of the extended chart, regarded over `K`. -/
instance instNormedAlgebraRationalChart :
    NormedAlgebra K (rationalChart K L d).algebra :=
  NormedAlgebra.restrictScalars K L (rationalChart K L d).algebra

instance instIsScalarTowerRationalChart :
    IsScalarTower K L (rationalChart K L d).algebra :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- The fraction coordinates of the extended chart. -/
def extendedFraction (j : Fin d.arity) : (rationalChart K L d).algebra :=
  RationalPresentation.fraction L (algebra K L A) d.radii
    (extendSeries K L d.denominator) (fun j => extendSeries K L (d.numerators j)) j

/-- The extended fraction coordinates satisfy the weighted monomial bound. -/
theorem extendedFraction_hasBoundedMonomials :
    HasBoundedMonomials d.radii (rationalChart K L d).algebra (extendedFraction K L d) := by
  refine ⟨1, one_pos, fun e => ?_⟩
  rw [one_mul]
  exact monomialValue_norm_le_weight d.radii (rationalChart K L d).algebra
    (PresentedAffinoidAlgebra.norm_one_le L (rationalChart K L d).algebra)
    (extendedFraction K L d)
    (RationalPresentation.norm_fraction_le L (algebra K L A) d.radii
      (extendSeries K L d.denominator) (fun j => extendSeries K L (d.numerators j))) e

/-- The structural map `A → A_L → (d_L).algebra`, over `K`. -/
def extendedBase : BoundedAlgHom K A (rationalChart K L d).algebra :=
  (overBase K L (rationalChart K L d).baseMap).comp (iota K L A)

theorem extendedBase_fraction_equation (j : Fin d.arity) :
    extendedBase K L d (presentationMap K A d.denominator) * extendedFraction K L d j =
      extendedBase K L d (presentationMap K A (d.numerators j)) :=
  RationalPresentation.fraction_equation L (algebra K L A) d.radii
    (extendSeries K L d.denominator) (fun j => extendSeries K L (d.numerators j)) j

/-- The images in `(d.algebra)_L` of the fraction coordinates of `d`. -/
def baseFraction (j : Fin d.arity) : algebra K L d.algebra :=
  iota K L d.algebra (chartFraction K d j)

theorem baseFraction_hasBoundedMonomials :
    HasBoundedMonomials d.radii (algebra K L d.algebra) (baseFraction K L d) :=
  RationalPresentation.hasBoundedMonomials_map_fraction K A d.radii d.denominator
    d.numerators (algebra K L d.algebra) (iota K L d.algebra)

variable [CompleteSpace L]

/-- The `K`-linear comparison map `d.algebra → (d_L).algebra`. -/
def toExtendedChart : BoundedAlgHom K d.algebra (rationalChart K L d).algebra :=
  RationalPresentation.liftFromBase K A d.radii d.denominator d.numerators
    (rationalChart K L d).algebra (extendedBase K L d) (extendedFraction K L d)
    (extendedFraction_hasBoundedMonomials K L d) (extendedBase_fraction_equation K L d)

theorem toExtendedChart_baseMap (a : A) :
    toExtendedChart K L d (d.baseMap a) = (rationalChart K L d).baseMap (iota K L A a) :=
  congrArg (fun φ : BoundedAlgHom K A (rationalChart K L d).algebra => φ a)
    (RationalPresentation.liftFromBase_comp_baseMap K A d.radii d.denominator d.numerators
      (rationalChart K L d).algebra (extendedBase K L d) (extendedFraction K L d)
      (extendedFraction_hasBoundedMonomials K L d) (extendedBase_fraction_equation K L d))

theorem toExtendedChart_fraction (j : Fin d.arity) :
    toExtendedChart K L d (chartFraction K d j) = extendedFraction K L d j :=
  RationalPresentation.liftFromBase_fraction K A d.radii d.denominator d.numerators
    (rationalChart K L d).algebra (extendedBase K L d) (extendedFraction K L d)
    (extendedFraction_hasBoundedMonomials K L d) (extendedBase_fraction_equation K L d) j

/-- The `L`-linear comparison map `(d.algebra)_L → (d_L).algebra`. -/
def forward : BoundedAlgHom L (algebra K L d.algebra) (rationalChart K L d).algebra :=
  lift K L d.algebra (rationalChart K L d).algebra (toExtendedChart K L d)

theorem forward_iota (x : d.algebra) :
    forward K L d (iota K L d.algebra x) = toExtendedChart K L d x :=
  lift_iota K L d.algebra (rationalChart K L d).algebra (toExtendedChart K L d) x

theorem map_fraction_equation (j : Fin d.arity) :
    map K L d.baseMap (presentationMap L (algebra K L A) (extendSeries K L d.denominator)) *
        baseFraction K L d j =
      map K L d.baseMap
        (presentationMap L (algebra K L A) (extendSeries K L (d.numerators j))) := by
  rw [presentationMap_extendSeries, presentationMap_extendSeries, map_iota, map_iota]
  refine ((iota K L d.algebra).toAlgHom.map_mul _ _).symm.trans ?_
  exact congrArg (iota K L d.algebra) (chartFraction_equation K d j)

/-- The `L`-linear comparison map `(d_L).algebra → (d.algebra)_L`. -/
def backward : BoundedAlgHom L (rationalChart K L d).algebra (algebra K L d.algebra) :=
  RationalPresentation.liftFromBase L (algebra K L A) d.radii
    (extendSeries K L d.denominator) (fun j => extendSeries K L (d.numerators j))
    (algebra K L d.algebra) (map K L d.baseMap) (baseFraction K L d)
    (baseFraction_hasBoundedMonomials K L d) (map_fraction_equation K L d)

theorem backward_comp_baseMap :
    (backward K L d).comp (rationalChart K L d).baseMap = map K L d.baseMap :=
  RationalPresentation.liftFromBase_comp_baseMap L (algebra K L A) d.radii
    (extendSeries K L d.denominator) (fun j => extendSeries K L (d.numerators j))
    (algebra K L d.algebra) (map K L d.baseMap) (baseFraction K L d)
    (baseFraction_hasBoundedMonomials K L d) (map_fraction_equation K L d)

theorem backward_baseMap (x : algebra K L A) :
    backward K L d ((rationalChart K L d).baseMap x) = map K L d.baseMap x :=
  congrArg (fun φ : BoundedAlgHom L (algebra K L A) (algebra K L d.algebra) => φ x)
    (backward_comp_baseMap K L d)

theorem backward_fraction (j : Fin d.arity) :
    backward K L d (extendedFraction K L d j) = baseFraction K L d j :=
  RationalPresentation.liftFromBase_fraction L (algebra K L A) d.radii
    (extendSeries K L d.denominator) (fun j => extendSeries K L (d.numerators j))
    (algebra K L d.algebra) (map K L d.baseMap) (baseFraction K L d)
    (baseFraction_hasBoundedMonomials K L d) (map_fraction_equation K L d) j

theorem backward_comp_forward :
    (backward K L d).comp (forward K L d) = BoundedAlgHom.id L (algebra K L d.algebra) := by
  apply hom_ext K L d.algebra
  apply RationalPresentation.hom_ext_base_fraction K A d.radii d.denominator d.numerators
  · apply BoundedAlgHom.ext
    intro a
    change backward K L d (forward K L d (iota K L d.algebra (d.baseMap a))) =
      iota K L d.algebra (d.baseMap a)
    rw [forward_iota, toExtendedChart_baseMap, backward_baseMap, map_iota]
  · intro j
    change backward K L d (forward K L d (iota K L d.algebra (chartFraction K d j))) =
      iota K L d.algebra (chartFraction K d j)
    rw [forward_iota, toExtendedChart_fraction, backward_fraction]
    rfl

theorem backward_forward (x : algebra K L d.algebra) :
    backward K L d (forward K L d x) = x :=
  calc backward K L d (forward K L d x)
      = ((backward K L d).comp (forward K L d)) x := (BoundedAlgHom.comp_apply _ _ x).symm
    _ = BoundedAlgHom.id L (algebra K L d.algebra) x :=
        congrArg (fun φ : BoundedAlgHom L (algebra K L d.algebra) (algebra K L d.algebra) =>
          φ x) (backward_comp_forward K L d)
    _ = x := BoundedAlgHom.id_apply x

theorem forward_comp_backward :
    (forward K L d).comp (backward K L d) =
      BoundedAlgHom.id L (rationalChart K L d).algebra := by
  apply RationalPresentation.hom_ext_base_fraction L (algebra K L A) d.radii
    (extendSeries K L d.denominator) (fun j => extendSeries K L (d.numerators j))
  · apply hom_ext K L A
    apply BoundedAlgHom.ext
    intro a
    change forward K L d (backward K L d ((rationalChart K L d).baseMap (iota K L A a))) =
      (rationalChart K L d).baseMap (iota K L A a)
    rw [backward_baseMap, map_iota, forward_iota, toExtendedChart_baseMap]
  · intro j
    change forward K L d (backward K L d (extendedFraction K L d j)) =
      extendedFraction K L d j
    rw [backward_fraction, baseFraction, forward_iota, toExtendedChart_fraction]

theorem forward_backward (y : (rationalChart K L d).algebra) :
    forward K L d (backward K L d y) = y :=
  calc forward K L d (backward K L d y)
      = ((forward K L d).comp (backward K L d)) y := (BoundedAlgHom.comp_apply _ _ y).symm
    _ = BoundedAlgHom.id L (rationalChart K L d).algebra y :=
        congrArg (fun φ : BoundedAlgHom L (rationalChart K L d).algebra
          (rationalChart K L d).algebra => φ y) (forward_comp_backward K L d)
    _ = y := BoundedAlgHom.id_apply y

/-- The bounded `L`-algebra equivalence `(d_L).algebra ≃ (d.algebra)_L` over `A_L`. -/
def chartEquiv :
    BoundedAlgEquiv L (rationalChart K L d).algebra (algebra K L d.algebra) :=
  BoundedAlgEquiv.ofHomInv (backward K L d) (forward K L d)
    (forward_backward K L d) (backward_forward K L d)

theorem chartEquiv_comp_baseMap :
    (chartEquiv K L d).toBoundedAlgHom.comp (rationalChart K L d).baseMap =
      map K L d.baseMap :=
  backward_comp_baseMap K L d

/-- Ground field extension of a rational chart map represents the preimage of
the chart locus, against every presented `L`-affinoid test algebra. -/
theorem represents_map_baseMap :
    Represents L (map K L d.baseMap) (spectrumProjection K L A ⁻¹' d.locus) := by
  have h := (RationalChart.represents (rationalChart K L d)).postcomp_equiv (chartEquiv K L d)
  rw [chartEquiv_comp_baseMap] at h
  exact h

/-- The spectrum map of `map K L d.baseMap` factors through the spectrum
homeomorphism of the chart comparison and the extended chart. -/
theorem spectrumMap_spectrumHomeomorph (x : BanachSpectrum (algebra K L d.algebra)) :
    (rationalChart K L d).spectrumMap ((chartEquiv K L d).spectrumHomeomorph x) =
      BanachSpectrum.comap (map K L d.baseMap).toBoundedRingHom x := by
  apply BanachSpectrum.ext
  intro a
  change x (backward K L d ((rationalChart K L d).baseMap a)) = x (map K L d.baseMap a)
  rw [backward_baseMap]

/-- The spectrum map of the extended chart map is injective. -/
theorem comap_map_baseMap_injective :
    Function.Injective (BanachSpectrum.comap (map K L d.baseMap).toBoundedRingHom) := by
  intro x y hxy
  rw [← spectrumMap_spectrumHomeomorph, ← spectrumMap_spectrumHomeomorph] at hxy
  exact (chartEquiv K L d).spectrumHomeomorph.injective
    (RationalChart.spectrumMap_injective _ hxy)

end Comparison

end Langlands.Analytic.PresentedAffinoidAlgebra.GroundFieldExtension
