import Langlands.Representation.GodementJacquet.WhittakerAveraging
import Langlands.Representation.GodementJacquet.AnalyticData
import Langlands.Representation.RankinSelberg.HaarSymmetriesProof

/-!
# Paired compact averaging for matrix functional equations

The same normalized average is transported through inverse transpose. Every
integral comparison retains an explicit convergence hypothesis.
-/

noncomputable section

namespace Langlands.GodementJacquet

open MeasureTheory HarmonicAnalysis Whittaker RankinSelberg
open scoped ENNReal NNReal Pointwise

universe uG uF uV

section NormalizedAverage

variable {G : Type uG} [Group G] [MeasurableSpace G]

/-- Left averaging divided by the mass of the averaging set. -/
def normalizedLeftAverage (μ : Measure G) (Ω : Set G) (W : G → ℂ) : G → ℂ :=
  fun g => (μ.real Ω : ℂ)⁻¹ * ∫ x in Ω, W (x * g) ∂μ

variable [MeasurableMul₂ G] [MeasurableInv G]
  (μ : Measure G) [SFinite μ] [μ.IsMulLeftInvariant]

/-- Normalized averaging preserves a convergent weighted integral. -/
theorem normalizedLeftAverage_integral (Ω : Set G) (hΩm : MeasurableSet Ω)
    (hΩfin : μ Ω ≠ ⊤) (hΩpos : μ Ω ≠ 0)
    (a W : G → ℂ) (ha : ∀ x ∈ Ω, ∀ g, a (x * g) = a g)
    (hconv : Integrable (fun g => a g * W g) μ) :
    Integrable (fun g => a g * normalizedLeftAverage μ Ω W g) μ ∧
      ∫ g, a g * normalizedLeftAverage μ Ω W g ∂μ = ∫ g, a g * W g ∂μ := by
  have hmass : (μ.real Ω : ℂ) ≠ 0 := by
    rw [Ne, Complex.ofReal_eq_zero, measureReal_def, ENNReal.toReal_eq_zero_iff]
    exact not_or.mpr ⟨hΩpos, hΩfin⟩
  obtain ⟨hint, hval⟩ := leftAverage_integral μ Ω hΩm hΩfin a W ha hconv
  have hpt : (fun g => a g * normalizedLeftAverage μ Ω W g) =
      fun g => (μ.real Ω : ℂ)⁻¹ * (a g * ∫ x in Ω, W (x * g) ∂μ) := by
    funext g
    simp only [normalizedLeftAverage]
    ring
  rw [hpt]
  exact ⟨hint.const_mul _, by
    rw [integral_const_mul, hval, ← mul_assoc, inv_mul_cancel₀ hmass, one_mul]⟩

omit [MeasurableMul₂ G] [MeasurableInv G] [SFinite μ] [μ.IsMulLeftInvariant] in
/-- A measure-preserving automorphism carries the normalized average over its
preimage to the original average, including the exact volume normalization. -/
theorem normalizedLeftAverage_comp (e : G ≃* G)
    (he : MeasurePreserving e μ μ) (hemb : MeasurableEmbedding e)
    (Ω : Set G) (hΩm : MeasurableSet Ω) (W : G → ℂ) (g : G) :
    normalizedLeftAverage μ Ω W (e g) =
      normalizedLeftAverage μ (e ⁻¹' Ω) (W ∘ e) g := by
  have hmass : μ.real (e ⁻¹' Ω) = μ.real Ω := by
    simp only [measureReal_def, he.measure_preimage hΩm.nullMeasurableSet]
  have hint : (∫ x in e ⁻¹' Ω, W (e (x * g)) ∂μ) =
      ∫ x in Ω, W (x * e g) ∂μ := by
    simpa only [map_mul] using
      (he.restrict_preimage hΩm).integral_comp hemb (fun x => W (x * e g))
  simp only [normalizedLeftAverage, hmass, Function.comp_apply]
  rw [hint]

end NormalizedAverage

namespace Padic

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance comparisonAveragingTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance comparisonAveragingValuativeRel : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance comparisonAveragingLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance comparisonAveragingMeasurableSpace (n : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := borel _
local instance comparisonAveragingBorelSpace (n : ℕ) :
    BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
local instance comparisonAveragingSecondCountable (n : ℕ) :
    SecondCountableTopology (Langlands.GeneralLinear (n + 1) F.Carrier) :=
  F.canonicalTopologicalData.generalLinearSecondCountableTopology (n + 1)
local instance comparisonAveragingSigmaCompact (n : ℕ) :
    SigmaCompactSpace (Langlands.GeneralLinear (n + 1) F.Carrier) :=
  F.canonicalTopologicalData.generalLinearSigmaCompactSpace (n + 1)

variable {n : ℕ}

/-- Averaging a model vector gives an actual bi-smooth matrix coefficient on
that same model representation, normalized by the subgroup's Haar mass. -/
def averagedModelCoefficient (ψ : UnitaryAdditiveCharacter F.Carrier)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V)
    (hσ : IsSmooth σ) (ℓ : glFunctionals ψ n σ)
    (K : OpenSubgroup (Langlands.GeneralLinear (n + 1) F.Carrier))
    (hK : IsCompact (K : Set (Langlands.GeneralLinear (n + 1) F.Carrier)))
    (w : (glCoefficientModel ψ n σ ℓ).toSubmodule) :
    biSmoothMatrixCoefficients (V := (glCoefficientModel ψ n σ ℓ).toSubmodule)
      (glModelRepresentation ψ n σ ℓ) :=
  (generalLinearHaar F.Carrier n |>.real (K : Set _ ) : ℂ)⁻¹ •
    ⟨biSmoothCoefficient _ (modelSetIntegralDual F ψ σ hσ ℓ K hK)
      ⟨w, glModel_isSmooth ψ n σ hσ ℓ w⟩,
      Submodule.subset_span ⟨_, _, rfl⟩⟩

@[simp]
theorem averagedModelCoefficient_apply (ψ : UnitaryAdditiveCharacter F.Carrier)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V)
    (hσ : IsSmooth σ) (ℓ : glFunctionals ψ n σ)
    (K : OpenSubgroup (Langlands.GeneralLinear (n + 1) F.Carrier))
    (hK : IsCompact (K : Set (Langlands.GeneralLinear (n + 1) F.Carrier)))
    (w : (glCoefficientModel ψ n σ ℓ).toSubmodule)
    (g : Langlands.GeneralLinear (n + 1) F.Carrier) :
    (averagedModelCoefficient F ψ σ hσ ℓ K hK w).val g =
      normalizedLeftAverage (generalLinearHaar F.Carrier n) (K : Set _)
        (glModelFunction ψ n σ ℓ w) g := rfl

/-- Normalized averaging preserves an actual full-matrix integral at every
parameter where the original integrand is integrable. -/
theorem matrixIntegral_normalizedLeftAverage
    (K : OpenSubgroup (Langlands.GeneralLinear (n + 1) F.Carrier))
    (hKc : IsCompact (K : Set (Langlands.GeneralLinear (n + 1) F.Carrier)))
    (Φ : MatrixTestFunction n F.Carrier)
    (hK : ∀ k ∈ K, (∀ M, Φ (k.val * M) = Φ M) ∧
      normalizedAbsoluteValue F.canonicalTopologicalData (Matrix.det k.val) = 1)
    (W : Langlands.GeneralLinear (n + 1) F.Carrier → ℂ) (s : ℂ)
    (hconv : MatrixConverges F Φ s W) :
    MatrixConverges F Φ s
        (normalizedLeftAverage (generalLinearHaar F.Carrier n) (K : Set _) W) ∧
      matrixIntegral F Φ s
        (normalizedLeftAverage (generalLinearHaar F.Carrier n) (K : Set _) W) =
        matrixIntegral F Φ s W := by
  let μ := generalLinearHaar F.Carrier n
  let abv := normalizedAbsoluteValue F.canonicalTopologicalData
  let a : Langlands.GeneralLinear (n + 1) F.Carrier → ℂ :=
    fun g => Φ g.val * determinantWeight abv g s
  have ha : ∀ x ∈ K, ∀ g, a (x * g) = a g := by
    intro x hx g
    obtain ⟨hΦx, hdet⟩ := hK x hx
    change Φ (x.val * g.val) * determinantWeight abv (x * g) s =
      Φ g.val * determinantWeight abv g s
    rw [hΦx, determinantWeight, determinantWeight, Units.val_mul,
      Matrix.det_mul, AbsoluteValue.map_mul, hdet, one_mul]
  have hint : Integrable (fun g => a g * W g) μ := by
    refine hconv.congr (Filter.Eventually.of_forall fun g => ?_)
    change Φ g.val * W g * determinantWeight abv g s =
      (Φ g.val * determinantWeight abv g s) * W g
    ring
  obtain ⟨hc, hv⟩ := normalizedLeftAverage_integral μ (K : Set _)
    K.isOpen.measurableSet hKc.measure_lt_top.ne
    (K.isOpen.measure_pos μ ⟨1, K.one_mem⟩).ne' a W ha hint
  have hpt (W' : Langlands.GeneralLinear (n + 1) F.Carrier → ℂ) :
      GodementJacquet.matrixIntegrand abv Φ s W' = fun g => a g * W' g := by
    funext g
    simp only [GodementJacquet.matrixIntegrand, a]
    ring
  constructor
  · change Integrable (GodementJacquet.matrixIntegrand abv Φ s _) μ
    rwa [hpt]
  · change (∫ g, GodementJacquet.matrixIntegrand abv Φ s _ g ∂μ) =
      ∫ g, GodementJacquet.matrixIntegrand abv Φ s W g ∂μ
    simpa only [hpt] using hv

/-- The compact open subgroup transported by inverse transpose. -/
def inverseTransposeOpenSubgroup
    (K : OpenSubgroup (Langlands.GeneralLinear (n + 1) F.Carrier)) :
    OpenSubgroup (Langlands.GeneralLinear (n + 1) F.Carrier) :=
  K.comap (GeneralLinear.inverseTranspose (n + 1) F.Carrier).toMonoidHom
    (GeneralLinear.continuous_inverseTranspose (n + 1) F.Carrier)

/-- The transported subgroup remains compact. -/
theorem isCompact_inverseTransposeOpenSubgroup
    (K : OpenSubgroup (Langlands.GeneralLinear (n + 1) F.Carrier))
    (hK : IsCompact (K : Set (Langlands.GeneralLinear (n + 1) F.Carrier))) :
    IsCompact (inverseTransposeOpenSubgroup F K :
      Set (Langlands.GeneralLinear (n + 1) F.Carrier)) := by
  exact ((GeneralLinear.inverseTransposeContinuous (n + 1) F.Carrier).toHomeomorph.isCompact_preimage).mpr hK

/-- The actual inverse-transpose transform of the averaged coefficient is the
normalized average of the transformed model function over the transported set. -/
theorem coefficientIota_averagedModelCoefficient
    (ψ : UnitaryAdditiveCharacter F.Carrier)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V)
    (hσ : IsSmooth σ) (ℓ : glFunctionals ψ n σ)
    (K : OpenSubgroup (Langlands.GeneralLinear (n + 1) F.Carrier))
    (hK : IsCompact (K : Set (Langlands.GeneralLinear (n + 1) F.Carrier)))
    (w : (glCoefficientModel ψ n σ ℓ).toSubmodule) :
    coefficientIota (averagedModelCoefficient F ψ σ hσ ℓ K hK w).val =
      normalizedLeftAverage (generalLinearHaar F.Carrier n)
        (inverseTransposeOpenSubgroup F K : Set _)
        (coefficientIota (glModelFunction ψ n σ ℓ w)) := by
  funext g
  change (averagedModelCoefficient F ψ σ hσ ℓ K hK w).val
    (GeneralLinear.inverseTranspose (n + 1) F.Carrier g) = _
  rw [averagedModelCoefficient_apply]
  exact normalizedLeftAverage_comp (generalLinearHaar F.Carrier n)
    (GeneralLinear.inverseTranspose (n + 1) F.Carrier)
    (generalLinearHaarSymmetries F.Carrier n).2.1
    ((GeneralLinear.inverseTransposeContinuous (n + 1) F.Carrier).toHomeomorph.measurableEmbedding) K K.isOpen.measurableSet _ g

/-- A single actual bi-smooth coefficient preserves both integrals, assuming
convergence of each original integrand and invariance of the respective tests. -/
theorem averagedModelCoefficient_paired_integrals
    (ψ : UnitaryAdditiveCharacter F.Carrier)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V)
    (hσ : IsSmooth σ) (ℓ : glFunctionals ψ n σ)
    (K : OpenSubgroup (Langlands.GeneralLinear (n + 1) F.Carrier))
    (hK : IsCompact (K : Set (Langlands.GeneralLinear (n + 1) F.Carrier)))
    (Φ ΦHat : MatrixTestFunction n F.Carrier)
    (hΦ : ∀ k ∈ K, (∀ M, Φ (k.val * M) = Φ M) ∧
      normalizedAbsoluteValue F.canonicalTopologicalData (Matrix.det k.val) = 1)
    (hΦHat : ∀ k ∈ inverseTransposeOpenSubgroup F K,
      (∀ M, ΦHat (k.val * M) = ΦHat M) ∧
      normalizedAbsoluteValue F.canonicalTopologicalData (Matrix.det k.val) = 1)
    (w : (glCoefficientModel ψ n σ ℓ).toSubmodule) (s t : ℂ)
    (hc : MatrixConverges F Φ s (glModelFunction ψ n σ ℓ w))
    (hcd : MatrixConverges F ΦHat t (coefficientIota (glModelFunction ψ n σ ℓ w))) :
    let f := averagedModelCoefficient F ψ σ hσ ℓ K hK w
    MatrixConverges F Φ s f.val ∧
      matrixIntegral F Φ s f.val = matrixIntegral F Φ s (glModelFunction ψ n σ ℓ w) ∧
      MatrixConverges F ΦHat t (coefficientIota f.val) ∧
      matrixIntegral F ΦHat t (coefficientIota f.val) =
        matrixIntegral F ΦHat t (coefficientIota (glModelFunction ψ n σ ℓ w)) := by
  have ho := matrixIntegral_normalizedLeftAverage F K hK Φ hΦ
    (glModelFunction ψ n σ ℓ w) s hc
  have hd := matrixIntegral_normalizedLeftAverage F (inverseTransposeOpenSubgroup F K)
    (isCompact_inverseTransposeOpenSubgroup F K hK) ΦHat hΦHat
    (coefficientIota (glModelFunction ψ n σ ℓ w)) t hcd
  have hf : (averagedModelCoefficient F ψ σ hσ ℓ K hK w).val =
      normalizedLeftAverage (generalLinearHaar F.Carrier n) (K : Set _)
        (glModelFunction ψ n σ ℓ w) := by
    funext g
    exact averagedModelCoefficient_apply F ψ σ hσ ℓ K hK w g
  dsimp only
  rw [hf]
  refine ⟨ho.1, ho.2, ?_⟩
  have hi := coefficientIota_averagedModelCoefficient F ψ σ hσ ℓ K hK w
  rw [hf] at hi
  rw [hi]
  exact hd

end Padic

end Langlands.GodementJacquet
