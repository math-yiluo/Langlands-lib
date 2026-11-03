import Langlands.Representation.Plancherel.DiscreteSeriesOrbitTopology
import Langlands.Representation.Plancherel.FiniteCharacterQuotientMeasure
import Mathlib.MeasureTheory.Integral.Lebesgue.Map

/-! # The locally preserved measure on an actual discrete-series twist orbit -/

noncomputable section

open Function Set Topology MeasureTheory MeasureTheory.Measure
open scoped ENNReal NNReal

namespace Langlands.Plancherel

/-- A homeomorphism of the target transports local measure preservation. -/
theorem IsLocallyMeasurePreserving.homeomorph_comp
    {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    [BorelSpace Y] [BorelSpace Z] {f : X → Y}
    {lambda : Measure X} {mu : Measure Y}
    (hf : IsLocallyMeasurePreserving f lambda mu) (e : Y ≃ₜ Z) :
    IsLocallyMeasurePreserving (e ∘ f) lambda (Measure.map e mu) := by
  intro x
  obtain ⟨U, hU, hx, hinj, hmeasure⟩ := hf x
  refine ⟨U, hU, hx, e.injective.injOn.comp hinj (mapsTo_univ _ _), ?_⟩
  intro E hE hsub
  obtain ⟨himage, heq⟩ := hmeasure E hE hsub
  have hm : MeasurableSet (e '' (f '' E)) :=
    e.measurableEmbedding.measurableSet_image' himage
  rw [image_comp]
  refine ⟨hm, ?_⟩
  rw [Measure.map_apply e.continuous.measurable hm, e.injective.preimage_image, heq]

universe uG uV uI

variable {G : Type uG} [Group G] [TopologicalSpace G] [NonarchimedeanGroup G]
variable {I : Type uI} (nu : I → (G →* ℝ≥0ˣ))

/-- Character integration uses the Borel sets of the compact-open topology. -/
instance unitaryUnramifiedCharactersMeasurableSpace :
    MeasurableSpace (unitaryUnramifiedCharacters nu) :=
  borel _

instance unitaryUnramifiedCharactersBorelSpace :
    BorelSpace (unitaryUnramifiedCharacters nu) :=
  ⟨rfl⟩

variable (A : Subgroup G) [A.Normal] (hA : A ≤ Subgroup.center G)
variable [MeasurableSpace (G ⧸ A)]
variable (mu : Measure (G ⧸ A)) [IsHaarMeasure mu]

/-- The actual orbit carries the Borel sets of its stabilizer-quotient topology. -/
instance discreteSeriesOrbitMeasurableSpace (omega : DiscreteSeriesClass A hA mu) :
    MeasurableSpace (discreteSeriesOrbit A hA mu nu omega) :=
  borel _

instance discreteSeriesOrbitBorelSpace (omega : DiscreteSeriesClass A hA mu) :
    BorelSpace (discreteSeriesOrbit A hA mu nu omega) :=
  ⟨rfl⟩

/-- The measure on the actual orbit, with the fixed scale of the supplied
character measure and counting measure on its finite fibers. -/
def discreteSeriesOrbitMeasure (omega : DiscreteSeriesClass A hA mu)
    [Finite (discreteSeriesStabilizer A hA mu nu omega)]
    (lambda : Measure (unitaryUnramifiedCharacters nu)) :
    Measure (discreteSeriesOrbit A hA mu nu omega) :=
  (Nat.card (discreteSeriesStabilizer A hA mu nu omega) : ℝ≥0∞)⁻¹ •
    Measure.map (discreteSeriesOrbitMap A hA mu nu omega) lambda

@[simp]
theorem discreteSeriesOrbitMeasure_apply (omega : DiscreteSeriesClass A hA mu)
    [Finite (discreteSeriesStabilizer A hA mu nu omega)]
    (lambda : Measure (unitaryUnramifiedCharacters nu))
    {E : Set (discreteSeriesOrbit A hA mu nu omega)} (hE : MeasurableSet E) :
    discreteSeriesOrbitMeasure nu A hA mu omega lambda E =
      (Nat.card (discreteSeriesStabilizer A hA mu nu omega) : ℝ≥0∞)⁻¹ *
        lambda (discreteSeriesOrbitMap A hA mu nu omega ⁻¹' E) := by
  rw [discreteSeriesOrbitMeasure, Measure.smul_apply,
    Measure.map_apply (continuous_discreteSeriesOrbitMap A hA mu nu omega).measurable hE]
  rfl

@[simp]
theorem discreteSeriesOrbitMeasure_univ (omega : DiscreteSeriesClass A hA mu)
    [Finite (discreteSeriesStabilizer A hA mu nu omega)]
    (lambda : Measure (unitaryUnramifiedCharacters nu)) :
    discreteSeriesOrbitMeasure nu A hA mu omega lambda univ =
      (Nat.card (discreteSeriesStabilizer A hA mu nu omega) : ℝ≥0∞)⁻¹ *
        lambda univ := by
  simp

theorem discreteSeriesOrbitMeasure_smul (omega : DiscreteSeriesClass A hA mu)
    [Finite (discreteSeriesStabilizer A hA mu nu omega)]
    (lambda : Measure (unitaryUnramifiedCharacters nu)) (c : ℝ≥0∞) :
    discreteSeriesOrbitMeasure nu A hA mu omega (c • lambda) =
      c • discreteSeriesOrbitMeasure nu A hA mu omega lambda := by
  simp only [discreteSeriesOrbitMeasure,
    Measure.map_smul c
      (continuous_discreteSeriesOrbitMap A hA mu nu omega).measurable.aemeasurable,
    smul_smul]
  rw [mul_comm]

/-- Transport through the existing actual orbit-stabilizer homeomorphism
agrees with the explicit orbit-map pushforward. -/
theorem discreteSeriesOrbitMeasure_eq_map_quotient
    (omega : DiscreteSeriesClass A hA mu)
    [Finite (discreteSeriesStabilizer A hA mu nu omega)]
    [MeasurableSpace
      ((unitaryUnramifiedCharacters nu) ⧸ discreteSeriesStabilizer A hA mu nu omega)]
    [BorelSpace
      ((unitaryUnramifiedCharacters nu) ⧸ discreteSeriesStabilizer A hA mu nu omega)]
    (lambda : Measure (unitaryUnramifiedCharacters nu)) :
    discreteSeriesOrbitMeasure nu A hA mu omega lambda =
      Measure.map (discreteSeriesOrbitHomeomorph A hA mu nu omega)
        (finiteCharacterQuotientMeasure (discreteSeriesStabilizer A hA mu nu omega) lambda) := by
  rw [finiteCharacterQuotientMeasure,
    Measure.map_smul _ (discreteSeriesOrbitHomeomorph A hA mu nu omega
      ).continuous.measurable.aemeasurable,
    Measure.map_map (discreteSeriesOrbitHomeomorph A hA mu nu omega).continuous.measurable
      QuotientGroup.continuous_mk.measurable]
  rfl

/-- Waldspurger VI.3's local-preservation convention for the actual twist map,
relative to the supplied invariant character measure. -/
theorem isLocallyMeasurePreserving_discreteSeriesOrbitMap
    (omega : DiscreteSeriesClass A hA mu)
    [Finite (discreteSeriesStabilizer A hA mu nu omega)]
    (lambda : Measure (unitaryUnramifiedCharacters nu)) [IsMulLeftInvariant lambda] :
    IsLocallyMeasurePreserving (discreteSeriesOrbitMap A hA mu nu omega) lambda
      (discreteSeriesOrbitMeasure nu A hA mu omega lambda) := by
  let : MeasurableSpace
      ((unitaryUnramifiedCharacters nu) ⧸ discreteSeriesStabilizer A hA mu nu omega) :=
    borel _
  let : BorelSpace
      ((unitaryUnramifiedCharacters nu) ⧸ discreteSeriesStabilizer A hA mu nu omega) :=
    ⟨rfl⟩
  rw [discreteSeriesOrbitMeasure_eq_map_quotient]
  exact (isLocallyMeasurePreserving_finiteCharacterQuotient
    (discreteSeriesStabilizer A hA mu nu omega) lambda).homeomorph_comp
      (discreteSeriesOrbitHomeomorph A hA mu nu omega)

/-- A commutative character group has the same stabilizer at every twist
of the base representation. -/
theorem discreteSeriesStabilizer_unitaryTwist
    (omega : DiscreteSeriesClass A hA mu) (chi : unitaryUnramifiedCharacters nu) :
    discreteSeriesStabilizer A hA mu nu (chi • omega) =
      discreteSeriesStabilizer A hA mu nu omega := by
  ext eta
  change eta • (chi • omega) = chi • omega ↔ eta • omega = omega
  rw [← mul_smul, mul_comm eta chi, mul_smul, smul_left_cancel_iff]

/-- The identity on representation classes transports the measure unchanged
when its base point is twisted by a character. -/
theorem map_discreteSeriesOrbitMeasure_baseChange
    (omega : DiscreteSeriesClass A hA mu) (chi : unitaryUnramifiedCharacters nu)
    [Finite (discreteSeriesStabilizer A hA mu nu omega)]
    [Finite (discreteSeriesStabilizer A hA mu nu (chi • omega))]
    (lambda : Measure (unitaryUnramifiedCharacters nu)) [IsMulLeftInvariant lambda] :
    Measure.map (discreteSeriesOrbitBaseChange A hA mu nu omega chi)
      (discreteSeriesOrbitMeasure nu A hA mu (chi • omega) lambda) =
        discreteSeriesOrbitMeasure nu A hA mu omega lambda := by
  have hcomp :
      (discreteSeriesOrbitBaseChange A hA mu nu omega chi) ∘
        discreteSeriesOrbitMap A hA mu nu (chi • omega) =
      (discreteSeriesOrbitMap A hA mu nu omega) ∘ (chi * ·) := by
    funext eta
    apply Subtype.ext
    change eta • (chi • omega) = (chi * eta) • omega
    rw [mul_comm chi eta, mul_smul]
  rw [discreteSeriesOrbitMeasure,
    Measure.map_smul _ (discreteSeriesOrbitBaseChange A hA mu nu omega chi
      ).continuous.measurable.aemeasurable,
    Measure.map_map (discreteSeriesOrbitBaseChange A hA mu nu omega chi).continuous.measurable
      (continuous_discreteSeriesOrbitMap A hA mu nu (chi • omega)).measurable,
    hcomp, ← Measure.map_map (f := fun eta => chi * eta)
      (continuous_discreteSeriesOrbitMap A hA mu nu omega).measurable
      (measurable_const_mul chi),
    map_mul_left_eq_self, discreteSeriesStabilizer_unitaryTwist]
  rfl

/-- Nonnegative integration along the actual character parameterization,
with its finite-fiber factor and the original character measure. -/
theorem lintegral_discreteSeriesOrbitMeasure
    (omega : DiscreteSeriesClass A hA mu)
    [Finite (discreteSeriesStabilizer A hA mu nu omega)]
    (lambda : Measure (unitaryUnramifiedCharacters nu))
    (f : discreteSeriesOrbit A hA mu nu omega → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ eta, f eta ∂discreteSeriesOrbitMeasure nu A hA mu omega lambda =
      (Nat.card (discreteSeriesStabilizer A hA mu nu omega) : ℝ≥0∞)⁻¹ *
        ∫⁻ chi, f (discreteSeriesOrbitMap A hA mu nu omega chi) ∂lambda := by
  rw [discreteSeriesOrbitMeasure, lintegral_smul_measure,
    lintegral_map hf (continuous_discreteSeriesOrbitMap A hA mu nu omega).measurable]
  rfl

end Langlands.Plancherel
