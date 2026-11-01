import Langlands.Geometry.Analytic.GeneralizedAffinoid.StrictBaseChangeAdjoin
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalChartNormalization
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalChartRingEvaluation
import Langlands.Geometry.Analytic.StrictTestDomain.RationalPullbackProof

/-! # The scalar-normalized rational chart comparison and additive retraction -/

noncomputable section

universe u v

namespace Langlands.Analytic

namespace GeneralizedTateAlgebra

variable {σ : Type*} (r : PositivePolyradius σ)
  {K : Type u} [NormedField K] [IsUltrametricDist K]
  {L : Type v} [NormedField L] [IsUltrametricDist L]
  (ι : K →+* L) (hι : ∀ a, ‖ι a‖ = ‖a‖)
  {c : σ → L} (hc : ∀ i, ‖c i‖ = r i)

/-- A normalized strict coordinate times its realizing scalar is the image of
an original weighted coordinate. -/
theorem baseChange_X (i : σ) :
    baseChange r ι hc hι (X r K i) =
      algebraMap L (StrictTateAlgebra σ L) (c i) * StrictTateAlgebra.X σ L i := by
  classical
  apply Subtype.ext
  apply MvPowerSeries.ext
  intro e
  change MvPowerSeries.coeff e (StrictTateAlgebra.series σ L
    (baseChange r ι hc hι (X r K i))) = _
  rw [coeff_baseChange]
  change scale c e * ι (MvPowerSeries.coeff e
    (MvPowerSeries.monomial (Finsupp.single i 1) 1)) =
      MvPowerSeries.coeff e (MvPowerSeries.C (c i) *
        MvPowerSeries.monomial (Finsupp.single i 1) 1)
  rw [MvPowerSeries.coeff_C_mul]
  by_cases he : e = Finsupp.single i 1
  · subst e
    simp [scale]
  · simp [MvPowerSeries.coeff_monomial, he]

end GeneralizedTateAlgebra

namespace PresentedAffinoidAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K]
  {L : Type v} [NormedField L] [IsUltrametricDist L]
  (A : PresentedAffinoidAlgebra K) (ι : K →+* L) (hι : ∀ a, ‖ι a‖ = ‖a‖)
  {c : Fin A.arity → L} (hc : ∀ i, ‖c i‖ = A.polyradius i)

theorem strictBaseChangeHom_coordinate (i : Fin A.arity) :
    strictBaseChangeHom A ι hι hc (coordinate K A i) =
      algebraMap L (strictBaseChange A ι hι hc) (c i) *
        PresentedStrictAffinoidAlgebra.coordinate L (strictBaseChange A ι hι hc) i := by
  change PresentedStrictAffinoidAlgebra.presentationMap L (strictBaseChange A ι hι hc)
    (GeneralizedTateAlgebra.baseChange A.polyradius ι hc hι
      (GeneralizedTateAlgebra.X A.polyradius K i)) = _
  rw [GeneralizedTateAlgebra.baseChange_X]
  exact ((PresentedStrictAffinoidAlgebra.presentationMap L
    (strictBaseChange A ι hι hc)).toAlgHom.map_mul _ _).trans
      (congrArg (fun a => a *
        PresentedStrictAffinoidAlgebra.coordinate L (strictBaseChange A ι hι hc) i)
          ((PresentedStrictAffinoidAlgebra.presentationMap L
            (strictBaseChange A ι hι hc)).toAlgHom.commutes (c i)))

/-- The scalar-change ring map with its contractive norm bound. -/
def strictBaseChangeBoundedHom : BoundedRingHom A (strictBaseChange A ι hι hc) where
  toRingHom := strictBaseChangeHom A ι hι hc
  bounded := ⟨1, zero_lt_one, fun a => by
    simpa only [one_mul] using norm_strictBaseChangeHom_le A ι hι hc a⟩

namespace RationalChart

open StrictTateAlgebra

variable {A} (d : RationalChart K A)
  {τ : Fin d.arity → L} (hτ : ∀ j, ‖τ j‖ = d.radii j)

/-- The strict scalar extension of the actual original rational quotient. -/
abbrev rawStrictScalarExtension : PresentedStrictAffinoidAlgebra L :=
  strictBaseChange d.algebra ι hι (Adjoin.norm_addCases A d.radii hc hτ)

/-- The strict scalar-change inclusion of the base into the actual enlarged
quotient. -/
def rawStrictBaseMap : BoundedAlgHom L (strictBaseChange A ι hι hc)
    (d.rawStrictScalarExtension ι hι hc hτ) :=
  Adjoin.strictBaseChangeMap A d.radii
    (RationalPresentation.equations K A d.radii d.denominator d.numerators) ι hι hc hτ

@[simp] theorem rawStrictBaseMap_scalar (a : A) :
    d.rawStrictBaseMap ι hι hc hτ (strictBaseChangeHom A ι hι hc a) =
      strictBaseChangeHom d.algebra ι hι (Adjoin.norm_addCases A d.radii hc hτ)
        (d.baseMap a) :=
  Adjoin.strictBaseChangeMap_strictBaseChangeHom A d.radii
    (RationalPresentation.equations K A d.radii d.denominator d.numerators)
    ι hι hc hτ a

/-- The newly adjoined normalized strict coordinate. -/
def rawStrictFraction (j : Fin d.arity) : d.rawStrictScalarExtension ι hι hc hτ :=
  PresentedStrictAffinoidAlgebra.coordinate L (d.rawStrictScalarExtension ι hι hc hτ)
    (Fin.natAdd A.arity j)

theorem scalar_fraction (j : Fin d.arity) :
    strictBaseChangeHom d.algebra ι hι (Adjoin.norm_addCases A d.radii hc hτ)
      (RationalPresentation.fraction K A d.radii d.denominator d.numerators j) =
        algebraMap L (d.rawStrictScalarExtension ι hι hc hτ) (τ j) *
          d.rawStrictFraction ι hι hc hτ j := by
  have h := strictBaseChangeHom_coordinate d.algebra ι hι
    (Adjoin.norm_addCases A d.radii hc hτ) (Fin.natAdd A.arity j)
  change _ = algebraMap L (d.rawStrictScalarExtension ι hι hc hτ)
    ((Fin.addCases c τ : Fin (A.arity + d.arity) → L) (Fin.natAdd A.arity j)) * _ at h
  exact h.trans (congrArg (fun a : L =>
    algebraMap L (d.rawStrictScalarExtension ι hι hc hτ) a *
      d.rawStrictFraction ι hι hc hτ j) (Fin.addCases_right j))

/-- The canonical strict normalization over the strict scalar extension of the
base algebra. -/
abbrev scalarNormalizedStrict [CompleteSpace L] : StrictTestDomain.RationalData L
    (strictBaseChange A ι hι hc) :=
  d.normalizedStrict (strictBaseChange A ι hι hc)
    (strictBaseChangeBoundedHom A ι hι hc) τ hτ

theorem rawStrictFraction_hasBoundedMonomials :
    HasBoundedMonomials (Fin d.arity) (d.rawStrictScalarExtension ι hι hc hτ)
      (d.rawStrictFraction ι hι hc hτ) := by
  apply (hasBoundedMonomials_iff_pow_bound (Fin d.arity) _ _).mpr
  intro j
  exact (StrictTateAlgebra.hasBoundedMonomials_map_X
    (Fin (d.rawStrictScalarExtension ι hι hc hτ).arity) L _
    (PresentedStrictAffinoidAlgebra.presentationMap L
      (d.rawStrictScalarExtension ι hι hc hτ))).pow_bound
        (Fin (d.rawStrictScalarExtension ι hι hc hτ).arity) _
          (Fin.natAdd A.arity j)

theorem rawStrictFraction_equation [CompleteSpace L] (j : Fin d.arity) :
    d.rawStrictBaseMap ι hι hc hτ (d.scalarNormalizedStrict ι hι hc hτ).denominator *
      d.rawStrictFraction ι hι hc hτ j =
        d.rawStrictBaseMap ι hι hc hτ
          ((d.scalarNormalizedStrict ι hι hc hτ).numerator j) := by
  let S := d.rawStrictScalarExtension ι hι hc hτ
  let E := strictBaseChangeHom d.algebra ι hι (Adjoin.norm_addCases A d.radii hc hτ)
  have heq :
      d.rawStrictBaseMap ι hι hc hτ
          (strictBaseChangeHom A ι hι hc (presentationMap K A d.denominator)) *
        (algebraMap L S (τ j) * d.rawStrictFraction ι hι hc hτ j) =
      d.rawStrictBaseMap ι hι hc hτ
        (strictBaseChangeHom A ι hι hc (presentationMap K A (d.numerators j))) := by
    rw [d.rawStrictBaseMap_scalar, d.rawStrictBaseMap_scalar, ← d.scalar_fraction]
    exact (E.map_mul _ _).symm.trans
      (congrArg E (RationalPresentation.fraction_equation K A d.radii
        d.denominator d.numerators j))
  have ht : τ j ≠ 0 := norm_pos_iff.mp (by rw [hτ]; exact d.radii.positive j)
  have hinv : algebraMap L S (τ j)⁻¹ * algebraMap L S (τ j) = 1 := by
    rw [← map_mul, inv_mul_cancel₀ ht, map_one]
  calc
    _ = (algebraMap L S (τ j)⁻¹ * algebraMap L S (τ j)) *
        (d.rawStrictBaseMap ι hι hc hτ
            (strictBaseChangeHom A ι hι hc (presentationMap K A d.denominator)) *
          d.rawStrictFraction ι hι hc hτ j) := by rw [hinv, one_mul]; rfl
    _ = algebraMap L S (τ j)⁻¹ *
        (d.rawStrictBaseMap ι hι hc hτ
            (strictBaseChangeHom A ι hι hc (presentationMap K A d.denominator)) *
          (algebraMap L S (τ j) * d.rawStrictFraction ι hι hc hτ j)) := by ring
    _ = algebraMap L S (τ j)⁻¹ *
        d.rawStrictBaseMap ι hι hc hτ
          (strictBaseChangeHom A ι hι hc (presentationMap K A (d.numerators j))) :=
      congrArg (fun x : S => algebraMap L S (τ j)⁻¹ * x) heq
    _ = _ := ((d.rawStrictBaseMap ι hι hc hτ).toAlgHom.map_mul
      (algebraMap L (strictBaseChange A ι hι hc) (τ j)⁻¹)
      (strictBaseChangeHom A ι hι hc (presentationMap K A (d.numerators j)))).trans
        (congrArg (fun x => x *
          d.rawStrictBaseMap ι hι hc hτ
            (strictBaseChangeHom A ι hι hc (presentationMap K A (d.numerators j))))
              ((d.rawStrictBaseMap ι hι hc hτ).toAlgHom.commutes (τ j)⁻¹)) |>.symm

/-- Compare the normalized strict rational quotient with the strict scalar
extension of the actual original rational quotient. -/
def scalarComparison [CompleteSpace L] :
    BoundedAlgHom L (d.scalarNormalizedStrict ι hι hc hτ).algebra
      (d.rawStrictScalarExtension ι hι hc hτ) :=
  RationalLocalization.liftFromBase L (strictBaseChange A ι hι hc) d.arity
    (d.scalarNormalizedStrict ι hι hc hτ).denominator
    (d.scalarNormalizedStrict ι hι hc hτ).numerator
    (d.rawStrictScalarExtension ι hι hc hτ) (d.rawStrictBaseMap ι hι hc hτ)
    (d.rawStrictFraction ι hι hc hτ)
    (d.rawStrictFraction_hasBoundedMonomials ι hι hc hτ)
    (d.rawStrictFraction_equation ι hι hc hτ)

@[simp] theorem scalarComparison_baseMap [CompleteSpace L]
    (a : strictBaseChange A ι hι hc) :
    d.scalarComparison ι hι hc hτ ((d.scalarNormalizedStrict ι hι hc hτ).baseMap a) =
      d.rawStrictBaseMap ι hι hc hτ a :=
  congrArg (fun f => f a)
    (RationalLocalization.liftFromBase_comp_baseMap L (strictBaseChange A ι hι hc)
      d.arity (d.scalarNormalizedStrict ι hι hc hτ).denominator
      (d.scalarNormalizedStrict ι hι hc hτ).numerator
      (d.rawStrictScalarExtension ι hι hc hτ) (d.rawStrictBaseMap ι hι hc hτ)
      (d.rawStrictFraction ι hι hc hτ)
      (d.rawStrictFraction_hasBoundedMonomials ι hι hc hτ)
      (d.rawStrictFraction_equation ι hι hc hτ))

@[simp] theorem scalarComparison_fraction [CompleteSpace L] (j : Fin d.arity) :
    d.scalarComparison ι hι hc hτ ((d.scalarNormalizedStrict ι hι hc hτ).fraction j) =
      d.rawStrictFraction ι hι hc hτ j :=
  RationalLocalization.liftFromBase_fractionCoordinate L (strictBaseChange A ι hι hc)
    d.arity (d.scalarNormalizedStrict ι hι hc hτ).denominator
    (d.scalarNormalizedStrict ι hι hc hτ).numerator
    (d.rawStrictScalarExtension ι hι hc hτ) (d.rawStrictBaseMap ι hι hc hτ)
    (d.rawStrictFraction ι hι hc hτ)
    (d.rawStrictFraction_hasBoundedMonomials ι hι hc hτ)
    (d.rawStrictFraction_equation ι hι hc hτ) j

/-- Any constructed forward map with the base square has the expected
composite with the comparison. -/
theorem scalarComparison_comp_map [CompleteSpace L]
    (F : BoundedRingHom d.algebra (d.scalarNormalizedStrict ι hι hc hτ).algebra)
    (hF : ∀ a, F (d.baseMap a) =
      (d.scalarNormalizedStrict ι hι hc hτ).baseMap (strictBaseChangeHom A ι hι hc a)) :
    (d.scalarComparison ι hι hc hτ).toBoundedRingHom.comp F =
      strictBaseChangeBoundedHom d.algebra ι hι (Adjoin.norm_addCases A d.radii hc hτ) := by
  apply d.ringHom_ext_over_base (d.rawStrictScalarExtension ι hι hc hτ)
    ((strictBaseChangeBoundedHom d.algebra ι hι
      (Adjoin.norm_addCases A d.radii hc hτ)).comp d.baseMap.toBoundedRingHom)
    (fun a => (norm_strictBaseChangeHom_le d.algebra ι hι
      (Adjoin.norm_addCases A d.radii hc hτ) (d.baseMap a)).trans
        (RationalPresentation.norm_baseMap_le K A d.radii d.denominator d.numerators a))
  · intro a
    change d.scalarComparison ι hι hc hτ (F (d.baseMap a)) =
      strictBaseChangeHom d.algebra ι hι (Adjoin.norm_addCases A d.radii hc hτ)
        (d.baseMap a)
    rw [hF, d.scalarComparison_baseMap, d.rawStrictBaseMap_scalar]
  · intro a
    rfl

variable (π : L →+ K) (hπ : ∀ a x, π (ι a * x) = a * π x)
  {D : ℝ} (hD : 0 ≤ D) (hπD : ∀ x, ‖π x‖ ≤ D * ‖x‖)

/-- Additive descent from the normalized strict rational quotient to the
original weighted rational quotient. -/
def scalarRetraction [CompleteSpace L] :
    (d.scalarNormalizedStrict ι hι hc hτ).algebra →+ d.algebra :=
  (strictBaseChangeRetraction d.algebra ι hι (Adjoin.norm_addCases A d.radii hc hτ)
    π hπ hD hπD).comp (d.scalarComparison ι hι hc hτ).toAlgHom.toRingHom.toAddMonoidHom

theorem scalarRetraction_baseMap [CompleteSpace L] (a : strictBaseChange A ι hι hc) :
    d.scalarRetraction ι hι hc hτ π hπ hD hπD
        ((d.scalarNormalizedStrict ι hι hc hτ).baseMap a) =
      d.baseMap (strictBaseChangeRetraction A ι hι hc π hπ hD hπD a) := by
  change strictBaseChangeRetraction d.algebra ι hι (Adjoin.norm_addCases A d.radii hc hτ)
    π hπ hD hπD
    (d.scalarComparison ι hι hc hτ ((d.scalarNormalizedStrict ι hι hc hτ).baseMap a)) = _
  rw [d.scalarComparison_baseMap]
  exact Adjoin.strictBaseChangeRetraction_baseMap A d.radii
    (RationalPresentation.equations K A d.radii d.denominator d.numerators)
    ι hι hc hτ π hπ hD hπD a

theorem scalarRetraction_map [CompleteSpace L] (hπ1 : π 1 = 1)
    (F : BoundedRingHom d.algebra (d.scalarNormalizedStrict ι hι hc hτ).algebra)
    (hF : ∀ a, F (d.baseMap a) =
      (d.scalarNormalizedStrict ι hι hc hτ).baseMap (strictBaseChangeHom A ι hι hc a))
    (a : d.algebra) :
    d.scalarRetraction ι hι hc hτ π hπ hD hπD (F a) = a := by
  have h := congrArg (fun f : BoundedRingHom d.algebra
      (d.rawStrictScalarExtension ι hι hc hτ) => f a)
    (d.scalarComparison_comp_map ι hι hc hτ F hF)
  change strictBaseChangeRetraction d.algebra ι hι (Adjoin.norm_addCases A d.radii hc hτ)
    π hπ hD hπD (d.scalarComparison ι hι hc hτ (F a)) = a
  exact (congrArg (strictBaseChangeRetraction d.algebra ι hι
    (Adjoin.norm_addCases A d.radii hc hτ) π hπ hD hπD) h).trans
      (strictBaseChangeRetraction_strictBaseChangeHom d.algebra ι hι
        (Adjoin.norm_addCases A d.radii hc hτ) π hπ hD hπD hπ1 a)

theorem norm_scalarRetraction_le [CompleteSpace L]
    (b : (d.scalarNormalizedStrict ι hι hc hτ).algebra) :
    ‖d.scalarRetraction ι hι hc hτ π hπ hD hπD b‖ ≤
      D * ‖d.scalarComparison ι hι hc hτ b‖ :=
  norm_strictBaseChangeRetraction_le d.algebra ι hι (Adjoin.norm_addCases A d.radii hc hτ)
    π hπ hD hπD (d.scalarComparison ι hι hc hτ b)

end RationalChart
end PresentedAffinoidAlgebra
end Langlands.Analytic
