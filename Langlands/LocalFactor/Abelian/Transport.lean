import Langlands.HarmonicAnalysis.ConductorTransport
import Langlands.LocalFactor.Abelian.Definitions

/-! # The actual abelian epsilon expression under field transport -/

noncomputable section

open MeasureTheory

namespace Langlands.PadicField.AbelianTransport

open HarmonicAnalysis ConductorTransport

universe u v

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p) (E : PadicField.{v} p)
  (e : F.Carrier ≃ₐ[Padic p] E.Carrier)

local instance : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance : TopologicalSpace E.Carrier := E.canonicalTopologicalData.topology
local instance : MeasurableSpace F.Carrier := borel F.Carrier
local instance : MeasurableSpace E.Carrier := borel E.Carrier
local instance : BorelSpace F.Carrier := ⟨rfl⟩
local instance : BorelSpace E.Carrier := ⟨rfl⟩
local instance : IsTopologicalRing F.Carrier := by
  let := F.canonicalTopologicalData.valuativeRel
  let := F.canonicalTopologicalData.localField
  infer_instance
local instance : IsTopologicalRing E.Carrier := by
  let := E.canonicalTopologicalData.valuativeRel
  let := E.canonicalTopologicalData.localField
  infer_instance

private theorem continuous_equiv : Continuous e := by
  let := F.canonicalNormedField
  let := E.canonicalNormedField
  exact (Weil.Local.extension_isometry F E e.toAlgHom).continuous

/-- Pushforward of the actual regular additive Haar measure by the field equivalence. -/
def haarMeasure (μ : AdditiveHaarMeasure F.Carrier) : AdditiveHaarMeasure E.Carrier :=
  FieldTransport.haarMeasure e.toRingEquiv
    (continuous_equiv F E e) (continuous_equiv E F e.symm) μ

@[simp] theorem haarMeasure_measure (μ : AdditiveHaarMeasure F.Carrier) :
    (haarMeasure F E e μ).measure = Measure.map e μ.measure := rfl

private def fieldHomeomorph : F.Carrier ≃ₜ E.Carrier :=
  FieldTransport.homeomorph e.toRingEquiv
    (continuous_equiv F E e) (continuous_equiv E F e.symm)

/-- Change of variables for any set integral using the pushed-forward measure. -/
theorem setIntegral_haarMeasure (μ : AdditiveHaarMeasure F.Carrier)
    (g : E.Carrier → ℂ) (s : Set E.Carrier) :
    (∫ y in s, g y ∂(haarMeasure F E e μ).measure) =
      ∫ x in e ⁻¹' s, g (e x) ∂μ.measure :=
  (fieldHomeomorph F E e).measurableEmbedding.setIntegral_map g s

/-- The actual integer ring is the preimage of the target integer ring. -/
theorem preimage_integers :
    e ⁻¹' (E.canonicalTopologicalData.Integers : Set E.Carrier) =
      (F.canonicalTopologicalData.Integers : Set F.Carrier) := by
  ext x
  change e x ∈ E.canonicalTopologicalData.Integers ↔ x ∈ F.canonicalTopologicalData.Integers
  rw [E.canonicalTopologicalData.mem_integers_iff_discreteValuation_le_one,
    F.canonicalTopologicalData.mem_integers_iff_discreteValuation_le_one,
    CanonicalTransport.discreteValuation_map]

/-- The finite integer-ring volume is preserved under pushforward. -/
theorem integerVolume_eq (μ : AdditiveHaarMeasure F.Carrier) :
    E.canonicalTopologicalData.integerVolume (haarMeasure F E e μ) =
      F.canonicalTopologicalData.integerVolume μ := by
  unfold TopologicalData.integerVolume Measure.real
  have hmap := (fieldHomeomorph F E e).measurableEmbedding.map_apply μ.measure
    (E.canonicalTopologicalData.Integers : Set E.Carrier)
  change (Measure.map e μ.measure) (E.canonicalTopologicalData.Integers : Set E.Carrier) =
    μ.measure (e ⁻¹' (E.canonicalTopologicalData.Integers : Set E.Carrier)) at hmap
  rw [haarMeasure_measure, hmap, preimage_integers]

/-- Valuation shells correspond at the same integer index. -/
theorem preimage_valuationShell (k : ℤ) :
    e ⁻¹' E.canonicalTopologicalData.valuationShell k =
      F.canonicalTopologicalData.valuationShell k := by
  ext x
  simp only [Set.mem_preimage, TopologicalData.valuationShell, Set.mem_ofPred_eq,
    CanonicalTransport.discreteValuation_map]

/-- The shell selected by both actual conductors corresponds exactly. -/
theorem preimage_epsilonShell (χ : Quasicharacter F.Carrier)
    (ψ : UnitaryAdditiveCharacter F.Carrier) :
    e ⁻¹' E.canonicalTopologicalData.epsilonShell
      (quasicharacter F E e χ) (additiveCharacter F E e ψ) =
        F.canonicalTopologicalData.epsilonShell χ ψ := by
  simp only [TopologicalData.epsilonShell, additiveConductor_eq,
    multiplicativeConductor_eq, preimage_valuationShell]

/-- The zero extension of the transported quasicharacter agrees on all field elements. -/
theorem extendZero_map (χ : Quasicharacter F.Carrier) (x : F.Carrier) :
    Quasicharacter.extendZero (quasicharacter F E e χ) (e x) =
      Quasicharacter.extendZero χ x := by
  by_cases hx : x = 0
  · simp [hx]
  have he : e x ≠ 0 := by simpa only [map_zero] using e.injective.ne hx
  have hu : (unitsEquiv F E e).symm (Units.mk0 (e x) he) = Units.mk0 x hx := by
    apply Units.ext
    exact e.symm_apply_apply x
  simp only [Quasicharacter.extendZero, dite_eq_right hx, dite_eq_right he,
    quasicharacter_apply, hu]

/-- The plus-sign epsilon integrand agrees after the same change of variables. -/
theorem epsilonIntegrand_map (χ : Quasicharacter F.Carrier)
    (ψ : UnitaryAdditiveCharacter F.Carrier) (x : F.Carrier) :
    Quasicharacter.epsilonIntegrand (quasicharacter F E e χ)
      (additiveCharacter F E e ψ) (e x) =
        Quasicharacter.epsilonIntegrand χ ψ x := by
  simp only [Quasicharacter.epsilonIntegrand, extendZero_map,
    UnitaryAdditiveCharacter.complex_apply, additiveCharacter_apply, e.symm_apply_apply]

/-- The actual convergent Gauss integral is invariant under field transport. -/
theorem abelianGaussIntegral_eq (χ : Quasicharacter F.Carrier)
    (ψ : UnitaryAdditiveCharacter F.Carrier) (μ : AdditiveHaarMeasure F.Carrier) :
    E.canonicalTopologicalData.abelianGaussIntegral (quasicharacter F E e χ)
      (additiveCharacter F E e ψ) (haarMeasure F E e μ) =
        F.canonicalTopologicalData.abelianGaussIntegral χ ψ μ := by
  unfold TopologicalData.abelianGaussIntegral
  rw [setIntegral_haarMeasure, preimage_epsilonShell]
  simp only [epsilonIntegrand_map]

/-- Both branches of the actual measure-dependent abelian epsilon expression agree.
The unramified branch uses scale independence, not equality of chosen scales. -/
theorem abelianEpsilonExpression_eq (χ : Quasicharacter F.Carrier)
    (ψ : UnitaryAdditiveCharacter F.Carrier) (μ : AdditiveHaarMeasure F.Carrier) :
    E.canonicalTopologicalData.abelianEpsilonExpression (quasicharacter F E e χ)
      (additiveCharacter F E e ψ) (haarMeasure F E e μ) =
        F.canonicalTopologicalData.abelianEpsilonExpression χ ψ μ := by
  by_cases hχ : F.canonicalTopologicalData.IsUnramifiedQuasicharacter χ
  · have hE := (isUnramifiedQuasicharacter_iff F E e χ).2 hχ
    let c := F.canonicalTopologicalData.abelianScale
      (F.canonicalTopologicalData.additiveConductor ψ)
    have hc : E.canonicalTopologicalData.discreteValuation
        (unitsEquiv F E e c : E.Carrier) =
        WithZero.exp (-E.canonicalTopologicalData.additiveConductor
          (additiveCharacter F E e ψ)) := by
      rw [unitsEquiv_apply, CanonicalTransport.discreteValuation_map,
        additiveConductor_eq]
      exact F.canonicalTopologicalData.abelianScale_value _
    rw [E.canonicalTopologicalData.abelianEpsilonExpression_unramified_scale
      _ _ _ hE (unitsEquiv F E e c) hc,
      F.canonicalTopologicalData.abelianEpsilonExpression_unramified χ ψ μ hχ]
    simp only [quasicharacter_apply, ContinuousMulEquiv.symm_apply_apply,
      unitsEquiv_apply, CanonicalTransport.normalizedAbs_map, integerVolume_eq]
    rfl
  · have hE := mt (isUnramifiedQuasicharacter_iff F E e χ).1 hχ
    rw [E.canonicalTopologicalData.abelianEpsilonExpression_ramified _ _ _ hE,
      F.canonicalTopologicalData.abelianEpsilonExpression_ramified χ ψ μ hχ,
      abelianGaussIntegral_eq]

end Langlands.PadicField.AbelianTransport
