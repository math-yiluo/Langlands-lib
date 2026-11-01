import Langlands.Representation.GodementJacquet.TateScalarMellin
import Langlands.Representation.GodementJacquet.TateScalarTransport
import Langlands.Representation.GodementJacquet.MatrixUnitValueProof
import Langlands.Representation.RankinSelberg.NormalizedGeneratorExistenceProof

/-! Actual rank-one matrix analytics from a proved scalar character action. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Langlands.GodementJacquet

open MeasureTheory HarmonicAnalysis RankinSelberg GeneralLinear

universe uF uV

section Algebra

variable {K : Type uF} [Field K] [TopologicalSpace K]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- The specified continuous character acts by scalars on the actual carrier. -/
def TateCharacterAction
    (σ : Representation ℂ (Langlands.GeneralLinear 1 K) V)
    (χ : Quasicharacter K) : Prop :=
  ∀ g v, σ g v = (χ (determinant g) : ℂ) • v

/-- Every translate of a character belongs to its one-dimensional span. -/
theorem tateCharacter_translationFinite (χ : Quasicharacter K) :
    FiniteDimensional ℂ (Submodule.span ℂ
      (Set.range fun b : Kˣ => fun a : Kˣ => (χ (b * a) : ℂ))) := by
  let η : Kˣ → ℂ := fun a => χ a
  apply Submodule.finiteDimensional_of_le (S₂ := ℂ ∙ η)
  apply Submodule.span_le.mpr
  rintro _ ⟨b, rfl⟩
  have heq : (fun a : Kˣ => (χ (b * a) : ℂ)) = (χ b : ℂ) • η := by
    funext a
    simp [η, smul_eq_mul]
  change (fun a : Kˣ => (χ (b * a) : ℂ)) ∈ ℂ ∙ η
  rw [heq]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self η)

/-- Scalar action determines every coefficient in the full bi-smooth span. -/
theorem tateCoefficient_eq
    (σ : Representation ℂ (Langlands.GeneralLinear 1 K) V)
    (χ : Quasicharacter K)
    (hact : TateCharacterAction σ χ)
    (f : biSmoothMatrixCoefficients σ) (g : Langlands.GeneralLinear 1 K) :
    f.val g = f.val 1 * (χ (determinant g) : ℂ) := by
  have hall : ∀ f ∈ biSmoothMatrixCoefficients σ, ∀ g, f g = f 1 *
      (χ (determinant g) : ℂ) := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem f hf =>
        obtain ⟨ℓ, v, rfl⟩ := hf
        intro g
        change ℓ.val (σ g v.val) = ℓ.val (σ 1 v.val) * _
        rw [hact, map_smul]
        simp [mul_comm]
    | zero => simp
    | add f h hf hh ihf ihh =>
        intro g
        change f g + h g = (f 1 + h 1) * _
        rw [ihf, ihh, add_mul]
    | smul c f hf ih =>
        intro g
        change c * f g = (c * f 1) * _
        rw [ih, mul_assoc]
  exact hall f.val f.property g

omit [TopologicalSpace K] in
/-- In rank one, transpose does not change the inverse matrix. -/
theorem tateInverseTranspose_eq_inv (g : Langlands.GeneralLinear 1 K) :
    inverseTranspose 1 K g = g⁻¹ := by
  apply Units.ext
  ext i j
  change (g⁻¹) j i = (g⁻¹) i j
  rw [Subsingleton.elim j i]

/-- Pullback by inverse transpose changes scalar action to the inverse
character, on the original carrier. -/
theorem tateInverseTranspose_action
    (σ : Representation ℂ (Langlands.GeneralLinear 1 K) V)
    (χ : Quasicharacter K)
    (hact : TateCharacterAction σ χ) :
    ∀ g v, (σ.comp (inverseTranspose 1 K).toMonoidHom) g v =
      ((χ⁻¹) (determinant g) : ℂ) • v := by
  intro g v
  change σ (inverseTranspose 1 K g) v = _
  rw [hact, tateInverseTranspose_eq_inv, map_inv, map_inv]
  rfl

end Algebra

namespace Padic

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance tateAnalyticsTopology : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance tateAnalyticsValuation : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
local instance tateAnalyticsLocalField : IsNonarchimedeanLocalField F.Carrier := F.canonicalTopologicalData.localField
local instance tateAnalyticsT2 : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance tateAnalyticsSecondCountable : SecondCountableTopology F.Carrier :=
  F.canonicalTopologicalData.secondCountableTopology
local instance tateAnalyticsMeasurable : MeasurableSpace F.Carrier := borel _
local instance tateAnalyticsBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance tateAnalyticsUnitsMeasurable : MeasurableSpace F.Carrierˣ := borel _
local instance tateAnalyticsUnitsBorel : BorelSpace F.Carrierˣ := ⟨rfl⟩
local instance tateAnalyticsGLMeasurable (n : ℕ) : MeasurableSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := borel _
local instance tateAnalyticsGLBorel (n : ℕ) : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩

/-- The scalar character has actual uniform Mellin analytic data. -/
theorem tateCharacter_mellinAnalyticData (χ : Quasicharacter F.Carrier) :
    ScalarMellinAnalyticData F.canonicalTopologicalData.residueCardinality
      F.canonicalTopologicalData.normalizedAbs (localMultiplicativeHaar F.Carrier)
      (fun a => (χ a : ℂ)) 1 :=
  scalarMellinAnalyticData_finiteFunction p F F.canonicalTopologicalData 1 zero_lt_one
    (fun a => (χ a : ℂ)) (Units.continuous_val.comp χ.continuous)
    (tateCharacter_translationFinite χ)

/-- Scalar and matrix integrands agree after absorbing the coefficient at one
into the genuine scalar test. -/
theorem tateMatrixIntegrand_eq_scalar (χ : Quasicharacter F.Carrier)
    (f : Langlands.GeneralLinear 1 F.Carrier → ℂ)
    (hf : ∀ g, f g = f 1 * (χ (determinant g) : ℂ))
    (Φ : MatrixTestFunction 0 F.Carrier) (s : ℂ) :
    (fun a => GodementJacquet.matrixIntegrand
      (normalizedAbsoluteValue F.canonicalTopologicalData) Φ s f
      (tateScalarEquiv F.Carrier a)) =
    scalarMellinIntegrand F.canonicalTopologicalData.normalizedAbs
      (fun a => (χ a : ℂ)) 1 (f 1 • tateScalarTest F.Carrier Φ) s := by
  funext a
  rw [GodementJacquet.matrixIntegrand, hf]
  simp [tateScalarEquiv, scalarMellinIntegrand, tateScalarTest_scalar,
    determinantWeight, determinant, scalar, Matrix.GeneralLinearGroup.coe_scalar,
    normalizedAbsoluteValue, mul_comm, mul_left_comm, mul_assoc]

/-- Equality of the actual integrals uses the exact canonical Haar transport. -/
theorem tateMatrixIntegral_eq_scalar (χ : Quasicharacter F.Carrier)
    (f : Langlands.GeneralLinear 1 F.Carrier → ℂ)
    (hf : ∀ g, f g = f 1 * (χ (determinant g) : ℂ))
    (Φ : MatrixTestFunction 0 F.Carrier) (s : ℂ) :
    matrixIntegral F Φ s f =
      scalarMellinIntegral F.canonicalTopologicalData.normalizedAbs
        (localMultiplicativeHaar F.Carrier) (fun a => (χ a : ℂ)) 1
        (f 1 • tateScalarTest F.Carrier Φ) s := by
  change (∫ g, GodementJacquet.matrixIntegrand _ Φ s f g ∂_) = _
  rw [← integral_tateScalarEquiv F, tateMatrixIntegrand_eq_scalar F χ f hf]
  rfl

/-- One convergence half-plane works for all tests and scalar multiples of
this character, before a coefficient family is specified. -/
theorem tateMatrix_characterConverges (χ : Quasicharacter F.Carrier) :
    ∃ c : ℝ, ∀ Φ : MatrixTestFunction 0 F.Carrier,
      ∀ f : Langlands.GeneralLinear 1 F.Carrier → ℂ,
      (∀ g, f g = f 1 * (χ (determinant g) : ℂ)) →
      ∀ s : ℂ, c < s.re → MatrixConverges F Φ (s + jpssShift 0) f := by
  obtain ⟨c, hc⟩ := (tateCharacter_mellinAnalyticData F χ).1
  refine ⟨c, fun Φ f hf s hs => ?_⟩
  apply (integrable_tateScalarEquiv_iff F _).mp
  rw [tateMatrixIntegrand_eq_scalar F χ f hf]
  simpa [jpssShift] using hc (f 1 • tateScalarTest F.Carrier Φ) s hs

/-- The rank-one shift is zero, and genuine convergence is already proved. -/
theorem tateHasShiftedRationalValue_iff (χ : Quasicharacter F.Carrier)
    (f : Langlands.GeneralLinear 1 F.Carrier → ℂ)
    (hf : ∀ g, f g = f 1 * (χ (determinant g) : ℂ))
    (Φ : MatrixTestFunction 0 F.Carrier) (R : RationalFunctions) :
    HasShiftedRationalValue F.canonicalTopologicalData.residueCardinality
      (normalizedAbsoluteValue F.canonicalTopologicalData)
      (generalLinearHaar F.Carrier 0) Φ f R ↔
    HasRationalContinuation F.canonicalTopologicalData.residueCardinality
      (scalarMellinIntegral F.canonicalTopologicalData.normalizedAbs
        (localMultiplicativeHaar F.Carrier) (fun a => (χ a : ℂ)) 1
        (f 1 • tateScalarTest F.Carrier Φ)) R := by
  have heq : (fun s => GodementJacquet.matrixIntegral
      (normalizedAbsoluteValue F.canonicalTopologicalData)
      (generalLinearHaar F.Carrier 0) Φ (s + jpssShift 0) f) =
      scalarMellinIntegral F.canonicalTopologicalData.normalizedAbs
        (localMultiplicativeHaar F.Carrier) (fun a => (χ a : ℂ)) 1
        (f 1 • tateScalarTest F.Carrier Φ) := by
    funext s
    simpa [jpssShift, matrixIntegral] using tateMatrixIntegral_eq_scalar F χ f hf Φ s
  unfold HasShiftedRationalValue
  rw [heq]
  exact and_iff_right (by
    obtain ⟨c, hc⟩ := tateMatrix_characterConverges F χ
    exact ⟨c, hc Φ f hf⟩)

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- A genuine coefficient equal to the character, obtained by normalizing a
nonzero smooth coefficient at the identity. -/
theorem exists_tateCharacterCoefficient [Nontrivial V]
    (σ : Representation ℂ (Langlands.GeneralLinear 1 F.Carrier) V)
    (χ : Quasicharacter F.Carrier) (hσ : IsSmooth σ)
    (hact : TateCharacterAction σ χ) :
    ∃ f : biSmoothMatrixCoefficients σ, ∀ g, f.val g = (χ (determinant g) : ℂ) := by
  obtain ⟨ℓ, v, h⟩ := exists_biSmoothCoefficient_ne_zero F σ hσ
  let f : biSmoothMatrixCoefficients σ :=
    (ℓ.val v.val)⁻¹ • ⟨biSmoothCoefficient σ ℓ v, Submodule.subset_span ⟨ℓ, v, rfl⟩⟩
  refine ⟨f, fun g => ?_⟩
  change (ℓ.val v.val)⁻¹ * ℓ.val (σ g v.val) = _
  rw [hact, map_smul, smul_eq_mul]
  field_simp

/-- Matrix and scalar rational-value families are equal before taking any span. -/
theorem tateMatrixRationalValues_eq_scalar [Nontrivial V]
    (σ : Representation ℂ (Langlands.GeneralLinear 1 F.Carrier) V)
    (χ : Quasicharacter F.Carrier) (hσ : IsSmooth σ)
    (hact : TateCharacterAction σ χ) :
    matrixRationalValues F σ =
      scalarMellinRationalValues F.canonicalTopologicalData.residueCardinality
        F.canonicalTopologicalData.normalizedAbs (localMultiplicativeHaar F.Carrier)
        (fun a => (χ a : ℂ)) 1 := by
  ext R
  constructor
  · rintro ⟨Φ, f, hR⟩
    exact ⟨f.val 1 • tateScalarTest F.Carrier Φ,
      (tateHasShiftedRationalValue_iff F χ f.val (tateCoefficient_eq σ χ hact f) Φ R).mp hR⟩
  · rintro ⟨φ, hR⟩
    obtain ⟨f, hf⟩ := exists_tateCharacterCoefficient F σ χ hσ hact
    let Φ : MatrixTestFunction 0 F.Carrier :=
      Hecke.TestFunction.pullback (tateMatrixScalarHomeomorph F.Carrier) φ
    have hf1 : f.val 1 = 1 := by simp [hf]
    have htest : f.val 1 • tateScalarTest F.Carrier Φ = φ := by
      rw [hf1, one_smul]
      exact (Hecke.TestFunction.pullback (tateMatrixScalarHomeomorph F.Carrier)).left_inv φ
    refine ⟨Φ, f, (tateHasShiftedRationalValue_iff F χ f.val
      (tateCoefficient_eq σ χ hact f) Φ R).mpr ?_⟩
    rwa [htest]

/-- Uniform matrix convergence, rationality and a normalized generator follow
from the scalar Mellin theorem and the attained unit value. -/
theorem exists_tateMatrixAnalyticAssertions [Nontrivial V]
    (σ : Representation ℂ (Langlands.GeneralLinear 1 F.Carrier) V)
    (χ : Quasicharacter F.Carrier) (hσ : IsSmooth σ)
    (hact : TateCharacterAction σ χ) :
    ∃ P : Polynomial ℂ, MatrixAnalyticAssertions F σ P := by
  have hdata := tateCharacter_mellinAnalyticData F χ
  have hvalues := tateMatrixRationalValues_eq_scalar F σ χ hσ hact
  have hden : HasCommonDenominator (matrixRationalValues F σ) := by
    rw [hvalues]
    exact hdata.2.2
  obtain ⟨P, hP⟩ := normalizedGeneratorExistence (matrixRationalValues F σ) hden
    (Submodule.subset_span (one_mem_matrixRationalValues F σ hσ))
  refine ⟨P, ?_, ?_, hP⟩
  · obtain ⟨c, hc⟩ := tateMatrix_characterConverges F χ
    exact ⟨c, fun Φ f => hc Φ f.val (tateCoefficient_eq σ χ hact f)⟩
  · intro Φ f
    obtain ⟨R, hR⟩ := hdata.2.1 (f.val 1 • tateScalarTest F.Carrier Φ)
    exact ⟨R, (tateHasShiftedRationalValue_iff F χ f.val
      (tateCoefficient_eq σ χ hact f) Φ R).mpr hR⟩

/-- The transformed value family is exactly the inverse-character Mellin
family, with the same Haar measure and spectral weight. -/
theorem tateIotaMatrixRationalValues_eq_scalar [Nontrivial V]
    (σ : Representation ℂ (Langlands.GeneralLinear 1 F.Carrier) V)
    (χ : Quasicharacter F.Carrier) (hσ : IsSmooth σ)
    (hact : TateCharacterAction σ χ) :
    iotaMatrixRationalValues F σ =
      scalarMellinRationalValues F.canonicalTopologicalData.residueCardinality
        F.canonicalTopologicalData.normalizedAbs (localMultiplicativeHaar F.Carrier)
        (fun a => ((χ⁻¹) a : ℂ)) 1 := by
  change GodementJacquet.iotaMatrixRationalValues _ _ _ σ = _
  rw [iotaMatrixRationalValues_eq_comp_inverseTranspose]
  exact tateMatrixRationalValues_eq_scalar F
    (σ.comp (inverseTranspose 1 F.Carrier).toMonoidHom) χ⁻¹
    (isSmooth_comp _ (continuous_inverseTranspose _ _) hσ)
    (tateInverseTranspose_action σ χ hact)

/-- Transformed convergence, rationality and normalized generation are
transported from the actual inverse-transpose pullback. -/
theorem exists_tateIotaMatrixAnalyticAssertions [Nontrivial V]
    (σ : Representation ℂ (Langlands.GeneralLinear 1 F.Carrier) V)
    (χ : Quasicharacter F.Carrier) (hσ : IsSmooth σ)
    (hact : TateCharacterAction σ χ) :
    ∃ PDual : Polynomial ℂ, IotaMatrixAnalyticAssertions F σ PDual := by
  obtain ⟨PDual, hPDual⟩ := exists_tateMatrixAnalyticAssertions F
    (σ.comp (inverseTranspose 1 F.Carrier).toMonoidHom) χ⁻¹
    (isSmooth_comp _ (continuous_inverseTranspose _ _) hσ)
    (tateInverseTranspose_action σ χ hact)
  exact ⟨PDual,
    (iotaMatrixAnalyticAssertions_iff_comp_inverseTranspose _ _ _ PDual).mpr hPDual⟩

end Padic

end Langlands.GodementJacquet
