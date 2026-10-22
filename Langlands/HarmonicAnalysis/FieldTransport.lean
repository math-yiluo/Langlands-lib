import Langlands.HarmonicAnalysis.CharacterTransport
import Langlands.Representation.Hecke.TestFunction

/-!
# Harmonic data under an actual continuous field isomorphism

Characters and functions use inverse pullback; Haar measures use pushforward.
The same ring equivalence controls all three constructions.
-/

noncomputable section

open MeasureTheory

universe uF uE

namespace Langlands.HarmonicAnalysis

namespace FieldTransport

variable {F : Type uF} {E : Type uE} [Field F] [Field E]
  [TopologicalSpace F] [TopologicalSpace E]
  (e : F ≃+* E) (he : Continuous e) (hi : Continuous e.symm)

/-- The homeomorphism with exactly the supplied field isomorphism's maps. -/
def homeomorph : F ≃ₜ E := ⟨e.toEquiv, he, hi⟩

/-- Inverse pullback preserves the given character's continuity and nontriviality. -/
def additiveCharacter (ψ : UnitaryAdditiveCharacter F) : UnitaryAdditiveCharacter E :=
  ψ.comapSurjective e.symm.toAddMonoidHom hi e.symm.surjective

@[simp]
theorem additiveCharacter_apply (ψ : UnitaryAdditiveCharacter F) (y : E) :
    additiveCharacter e hi ψ y = ψ (e.symm y) := rfl

@[simp]
theorem additiveCharacter_complex (ψ : UnitaryAdditiveCharacter F) (y : E) :
    (additiveCharacter e hi ψ).complex y = ψ.complex (e.symm y) := rfl

@[simp]
theorem additiveCharacter_symm (ψ : UnitaryAdditiveCharacter F) :
    additiveCharacter e.symm he (additiveCharacter e hi ψ) = ψ := by
  apply UnitaryAdditiveCharacter.ext
  intro x
  change ψ (e.symm (e x)) = ψ x
  exact congrArg ψ (e.symm_apply_apply x)

/-- Transport is an equivalence of the actual nontrivial character types. -/
def additiveCharacterEquiv : UnitaryAdditiveCharacter F ≃ UnitaryAdditiveCharacter E where
  toFun := additiveCharacter e hi
  invFun := additiveCharacter e.symm he
  left_inv := additiveCharacter_symm e he hi
  right_inv := additiveCharacter_symm e.symm hi he

/-- The test-function equivalence associated to the same field isomorphism. -/
def testFunctionEquiv : SchwartzBruhat F ≃ₗ[ℂ] SchwartzBruhat E :=
  Langlands.Hecke.TestFunction.pullback (homeomorph e he hi).symm

@[simp]
theorem testFunctionEquiv_apply (f : SchwartzBruhat F) (y : E) :
    testFunctionEquiv e he hi f y = f (e.symm y) := rfl

@[simp]
theorem testFunctionEquiv_symm_apply (g : SchwartzBruhat E) (x : F) :
    (testFunctionEquiv e he hi).symm g x = g (e x) := rfl

variable [IsTopologicalRing F] [IsTopologicalRing E]
  [MeasurableSpace F] [MeasurableSpace E] [BorelSpace F] [BorelSpace E]

/-- Pushforward of the actual regular additive Haar measure. -/
def haarMeasure (μ : AdditiveHaarMeasure F) : AdditiveHaarMeasure E where
  measure := Measure.map e μ.measure
  isAddHaar := e.toAddEquiv.isAddHaarMeasure_map μ.measure he hi
  regular := Measure.Regular.map (homeomorph e he hi)

@[simp]
theorem haarMeasure_measure (μ : AdditiveHaarMeasure F) :
    (haarMeasure e he hi μ).measure = Measure.map e μ.measure := rfl

@[simp]
theorem haarMeasure_symm (μ : AdditiveHaarMeasure F) :
    haarMeasure e.symm hi he (haarMeasure e he hi μ) = μ := by
  apply AdditiveHaarMeasure.ext
  exact (homeomorph e he hi).toMeasurableEquiv.map_symm_map

/-- Pushforward and inverse pushforward give an equivalence of regular Haar measures. -/
def haarMeasureEquiv : AdditiveHaarMeasure F ≃ AdditiveHaarMeasure E where
  toFun := haarMeasure e he hi
  invFun := haarMeasure e.symm hi he
  left_inv := haarMeasure_symm e he hi
  right_inv := haarMeasure_symm e.symm hi he

/-- Positive finite Haar scaling commutes with transport. -/
theorem haarMeasure_scale (μ : AdditiveHaarMeasure F) (c : NNReal) (hc : 0 < c) :
    haarMeasure e he hi (μ.scale c hc) = (haarMeasure e he hi μ).scale c hc := by
  apply AdditiveHaarMeasure.ext
  exact Measure.map_smul c he.measurable.aemeasurable

/-- Transport has no Jacobian scalar: the measure itself is pushed forward. -/
theorem integral_haarMeasure (μ : AdditiveHaarMeasure F) (g : E → ℂ) :
    (∫ y, g y ∂(haarMeasure e he hi μ).measure) = ∫ x, g (e x) ∂μ.measure :=
  (homeomorph e he hi).measurableEmbedding.integral_map g

/-- Integrability is preserved and reflected by this same transport. -/
theorem integrable_haarMeasure_iff (μ : AdditiveHaarMeasure F) (g : E → ℂ) :
    Integrable g (haarMeasure e he hi μ).measure ↔ Integrable (g ∘ e) μ.measure :=
  (homeomorph e he hi).measurableEmbedding.integrable_map_iff

/-- Change of variables for the plus-sign raw Fourier integral.
The formula holds for arbitrary functions, including the raw integral convention. -/
theorem fourierIntegral_transport (ψ : UnitaryAdditiveCharacter F)
    (μ : AdditiveHaarMeasure F) (f : F → ℂ) (y : E) :
    fourierIntegral (additiveCharacter e hi ψ) (haarMeasure e he hi μ)
      (f ∘ e.symm) y = fourierIntegral ψ μ f (e.symm y) := by
  unfold fourierIntegral
  rw [integral_haarMeasure]
  simp only [additiveCharacter_complex, map_mul, RingEquiv.symm_apply_apply,
    Function.comp_apply]

/-- The actual test-function Fourier transform commutes with transport. -/
theorem fourierTransform_transport (ψ : UnitaryAdditiveCharacter F)
    (μ : AdditiveHaarMeasure F) (f : SchwartzBruhat F) (y : E) :
    fourierTransform (additiveCharacter e hi ψ) (haarMeasure e he hi μ)
      (testFunctionEquiv e he hi f) y = fourierTransform ψ μ f (e.symm y) :=
  fourierIntegral_transport e he hi ψ μ f y

variable [LocallyCompactSpace F] [T2Space F] [TotallyDisconnectedSpace F]
  [LocallyCompactSpace E] [T2Space E] [TotallyDisconnectedSpace E]

/-- Transport preserves the convergence and reflection conditions in intrinsic self-duality. -/
theorem isSelfDual (ψ : UnitaryAdditiveCharacter F) (μ : AdditiveHaarMeasure F)
    (h : IsSelfDual ψ μ) :
    IsSelfDual (additiveCharacter e hi ψ) (haarMeasure e he hi μ) := by
  intro g
  obtain ⟨f, rfl⟩ := (testFunctionEquiv e he hi).surjective g
  constructor
  · intro y
    apply (integrable_haarMeasure_iff e he hi μ _).2
    simpa only [Function.comp_def, additiveCharacter_complex, map_mul,
      RingEquiv.symm_apply_apply, fourierTransform_transport] using (h f).1 (e.symm y)
  · intro y
    have hFour :
        fourierTransform (additiveCharacter e hi ψ) (haarMeasure e he hi μ)
          (testFunctionEquiv e he hi f) =
            (fourierTransform ψ μ f) ∘ e.symm :=
      funext (fourierTransform_transport e he hi ψ μ f)
    rw [hFour, fourierIntegral_transport]
    simpa only [testFunctionEquiv_apply, map_neg] using (h f).2 (e.symm y)

/-- Intrinsic self-duality is preserved and reflected, without choosing a measure. -/
theorem isSelfDual_iff (ψ : UnitaryAdditiveCharacter F) (μ : AdditiveHaarMeasure F) :
    IsSelfDual (additiveCharacter e hi ψ) (haarMeasure e he hi μ) ↔ IsSelfDual ψ μ := by
  constructor
  · intro h
    simpa only [additiveCharacter_symm, haarMeasure_symm] using
      isSelfDual e.symm hi he _ _ h
  · exact isSelfDual e he hi ψ μ

include he in
/-- The existence propositions correspond; neither side is asserted unconditionally. -/
theorem selfDualMeasureExists_iff (ψ : UnitaryAdditiveCharacter F) :
    SelfDualMeasureExists (additiveCharacter e hi ψ) ↔ SelfDualMeasureExists ψ := by
  constructor
  · rintro ⟨ν, hν⟩
    refine ⟨haarMeasure e.symm hi he ν, ?_⟩
    simpa only [additiveCharacter_symm] using isSelfDual e.symm hi he _ _ hν
  · rintro ⟨μ, hμ⟩
    exact ⟨haarMeasure e he hi μ, isSelfDual e he hi ψ μ hμ⟩

end FieldTransport

end Langlands.HarmonicAnalysis
