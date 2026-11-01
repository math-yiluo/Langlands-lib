import Langlands.Representation.GodementJacquet.SupercuspidalCutoffNonzeroOperator
import Langlands.Representation.GodementJacquet.FourierRegularMatrixTranslates
import Langlands.Representation.Hecke.IntegratedConvolution
import Langlands.Representation.OrbitSpan
import Langlands.Representation.RankinSelberg.EqualRankCharacterChange

/-! # Cyclic monomial outputs of Fourier-regular matrix tests -/

noncomputable section

namespace Langlands.GodementJacquet.Padic

open MeasureTheory HarmonicAnalysis RankinSelberg
open scoped NNReal

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance monomialTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance monomialValuativeRel : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance monomialLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance monomialT2 : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance monomialDisconnected : TotallyDisconnectedSpace F.Carrier :=
  (padicLatticeGeometry F F.canonicalTopologicalData).1
local instance monomialMeasurable : MeasurableSpace F.Carrier := borel _
local instance monomialBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance monomialGLMeasurable (n : ℕ) :
    MeasurableSpace (GeneralLinear (n + 1) F.Carrier) := borel _
local instance monomialGLBorel (n : ℕ) :
    BorelSpace (GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩

variable {n : ℕ}

/-- The exact determinant factor for the weighted left translate. -/
theorem weightedRegularMatrixTest_leftTranslate
    (a : GeneralLinear (n + 1) F.Carrier) (s : ℂ)
    (Φ : regularMatrixTests (K := F.Carrier) (n + 1)) :
    weightedRegularMatrixTest F s (regularMatrixTranslate a⁻¹ 1 Φ) =
      determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData) a s •
        Hecke.TestFunction.leftTranslate a (weightedRegularMatrixTest F s Φ) := by
  apply Hecke.TestFunction.ext
  intro g
  have hw := determinantWeight_mul
    (normalizedAbsoluteValue F.canonicalTopologicalData) a (a⁻¹ * g) s
  simp only [mul_inv_cancel_left] at hw
  simp only [weightedRegularMatrixTest_apply, regularMatrixTranslate_apply,
    Units.val_one, Matrix.mul_one]
  change Φ.val (a⁻¹.val * g.val) *
      determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData) g s =
    determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData) a s *
      (Φ.val (a⁻¹.val * g.val) *
        determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData) (a⁻¹ * g) s)
  rw [hw]
  ring

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- Left translation acts on the actual operator output by the representation
and its determinant weight. -/
theorem regularMatrixZetaOperator_leftTranslate
    (ρ : Representation ℂ (GeneralLinear (n + 1) F.Carrier) V)
    (hρ : IsSmooth ρ) (a : GeneralLinear (n + 1) F.Carrier) (s : ℂ)
    (Φ : regularMatrixTests (K := F.Carrier) (n + 1)) (v : V) :
    regularMatrixZetaOperator F ρ hρ s (regularMatrixTranslate a⁻¹ 1 Φ) v =
      determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData) a s •
        ρ a (regularMatrixZetaOperator F ρ hρ s Φ v) := by
  change Hecke.integratedAction (generalLinearHaar F.Carrier n) ρ hρ
      (weightedRegularMatrixTest F s (regularMatrixTranslate a⁻¹ 1 Φ)) v = _
  rw [weightedRegularMatrixTest_leftTranslate, map_smul, LinearMap.smul_apply,
    Hecke.integratedAction_leftTranslate]
  rfl

/-- A regular test supported on determinant norm one gives an operator
independent of the complex exponent. -/
theorem regularMatrixZetaOperator_eq_of_detNorm_support
    (ρ : Representation ℂ (GeneralLinear (n + 1) F.Carrier) V)
    (hρ : IsSmooth ρ)
    (Φ : regularMatrixTests (K := F.Carrier) (n + 1))
    (hΦ : ∀ g : GeneralLinear (n + 1) F.Carrier,
      F.canonicalTopologicalData.determinantNorm (n + 1) g ≠ 1 → Φ.val g.val = 0)
    (s t : ℂ) :
    regularMatrixZetaOperator F ρ hρ s Φ = regularMatrixZetaOperator F ρ hρ t Φ := by
  suffices weightedRegularMatrixTest F s Φ = weightedRegularMatrixTest F t Φ by
    exact congrArg (Hecke.integratedAction (generalLinearHaar F.Carrier n) ρ hρ) this
  apply Hecke.TestFunction.ext
  intro g
  simp only [weightedRegularMatrixTest_apply]
  by_cases hg : F.canonicalTopologicalData.determinantNorm (n + 1) g = 1
  · have hnorm : (normalizedAbsoluteValue F.canonicalTopologicalData)
        (Matrix.det g.val) = 1 :=
      congrArg (fun u : ℝ≥0ˣ => ((u : ℝ≥0) : ℝ)) hg
    simp [determinantWeight, hnorm]
  · rw [hΦ g hg, zero_mul, zero_mul]

variable {m : ℕ}

/-- For any nonzero smooth pairing, one Fourier-regular test has the same
nonzero output on the chosen vector at every exponent. -/
theorem exists_fourierRegular_constant_output_of_pairing
    (hm : 0 < m)
    (ρ : Representation ℂ (GeneralLinear (m + 1) F.Carrier) V)
    (hρ : GeneralLinear.IsSupercuspidal ρ)
    (ℓ : Module.Dual ℂ V) (hℓ : IsSmoothVector ρ.dual ℓ)
    (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier)
    (hsd : IsSelfDual ψ ν) (v : V) (hv : ℓ v ≠ 0) :
    ∃ Φ : fourierRegularMatrixTests (m + 1) ψ ν hsd, ∃ u : V,
      u ≠ 0 ∧ ∀ s : ℂ,
        regularMatrixZetaOperator F ρ hρ.1.1 s ⟨Φ.val, Φ.property.1⟩ v = u := by
  let T := F.canonicalTopologicalData
  let C := supercuspidalCutoffMatrixTest T (Nat.succ_pos m) ρ hρ ℓ hℓ v
  have hC : C ∈ fourierRegularMatrixTests (m + 1) ψ ν hsd :=
    supercuspidalCutoffMatrixTest_mem_fourierRegularMatrixTests
      T hm ψ ν hsd ρ hρ ℓ hℓ v
  let Φ : fourierRegularMatrixTests (m + 1) ψ ν hsd :=
    ⟨conjugateMatrixTest (m + 1) C,
      conjugate_mem_fourierRegularMatrixTests (m + 1) ψ ν hsd hC⟩
  let Ψ : regularMatrixTests (K := F.Carrier) (m + 1) := ⟨Φ.val, Φ.property.1⟩
  have hsupport : ∀ g : GeneralLinear (m + 1) F.Carrier,
      T.determinantNorm (m + 1) g ≠ 1 → Ψ.val g.val = 0 := by
    intro g hg
    change starRingEnd ℂ (C g.val) = 0
    rw [show C g.val = 0 from
      supercuspidalCutoffMatrixTest_apply_of_not_mem T (Nat.succ_pos m)
        ρ hρ ℓ hℓ v g hg, map_zero]
  let u := regularMatrixZetaOperator F ρ hρ.1.1 0 Ψ v
  refine ⟨Φ, u, ?_, fun s => ?_⟩
  · let f : GeneralLinear (m + 1) F.Carrier → ℂ := fun g => C g.val
    have hf : Continuous f := C.continuous.comp Units.continuous_val
    have hfc : HasCompactSupport f :=
      hasCompactSupport_restrict_of_mem_regularMatrixTests (m + 1) hC.1
    have hfone : f 1 = ℓ v := by
      change C (1 : GeneralLinear (m + 1) F.Carrier).val = _
      have he := supercuspidalCutoffMatrixTest_apply T (Nat.succ_pos m) ρ hρ ℓ hℓ v
        (1 : (T.determinantNorm (m + 1)).ker)
      simpa [C] using he
    have hpos : 0 < ∫ g, ‖f g‖ ^ 2 ∂generalLinearHaar F.Carrier m :=
      (hf.norm.pow 2).integral_pos_of_hasCompactSupport_nonneg_nonzero
        (hfc.comp_left (g := fun z : ℂ => ‖z‖ ^ 2) (by simp))
        (fun g => sq_nonneg _) (x := 1) (by
          simpa only [Pi.pow_apply, hfone, ne_eq, sq_eq_zero_iff, norm_eq_zero] using hv)
    have hi : matrixIntegral F Φ.val 0 (fun g => ℓ (ρ g v)) =
        ∫ g, ((‖f g‖ ^ 2 : ℝ) : ℂ) ∂generalLinearHaar F.Carrier m := by
      apply integral_congr_ae
      filter_upwards [] with g
      change starRingEnd ℂ (C g.val) * ℓ (ρ g v) *
        determinantWeight (normalizedAbsoluteValue T) g 0 = _
      by_cases hg : T.determinantNorm (m + 1) g = 1
      · have hc : C g.val = ℓ (ρ g v) :=
          supercuspidalCutoffMatrixTest_apply T (Nat.succ_pos m) ρ hρ ℓ hℓ v ⟨g, hg⟩
        rw [determinantWeight, Complex.cpow_zero, mul_one, ← hc]
        simpa only [Complex.ofReal_pow] using Complex.conj_mul' (C g.val)
      · have hc : C g.val = 0 :=
          supercuspidalCutoffMatrixTest_apply_of_not_mem T (Nat.succ_pos m)
            ρ hρ ℓ hℓ v g hg
        simp [hc, f]
    intro hu
    have hz : (∫ g, ((‖f g‖ ^ 2 : ℝ) : ℂ) ∂generalLinearHaar F.Carrier m) = 0 := by
      rw [← hi, ← regularMatrixZetaOperator_dual F ρ hρ.1.1 0 Ψ v ℓ]
      change ℓ u = 0
      rw [hu, map_zero]
    rw [integral_complex_ofReal] at hz
    exact hpos.ne' (Complex.ofReal_eq_zero.mp hz)
  · exact congrArg (fun A : Module.End ℂ V => A v)
      (regularMatrixZetaOperator_eq_of_detNorm_support F ρ hρ.1.1 Ψ hsupport s 0)

/-- Smooth dual separation supplies the nonzero pairing for every nonzero input
vector, retaining that same input in all the resulting operator evaluations. -/
theorem exists_fourierRegular_constant_output
    (hm : 0 < m)
    (ρ : Representation ℂ (GeneralLinear (m + 1) F.Carrier) V)
    (hρ : GeneralLinear.IsSupercuspidal ρ)
    (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier)
    (hsd : IsSelfDual ψ ν) (v : V) (hv : v ≠ 0) :
    ∃ Φ : fourierRegularMatrixTests (m + 1) ψ ν hsd, ∃ u : V,
      u ≠ 0 ∧ ∀ s : ℂ,
        regularMatrixZetaOperator F ρ hρ.1.1 s ⟨Φ.val, Φ.property.1⟩ v = u := by
  obtain ⟨ℓ, hℓ, hℓv⟩ := exists_smoothFunctional_ne_zero F ρ hρ.1.1 v hv
  exact exists_fourierRegular_constant_output_of_pairing F hm ρ hρ ℓ hℓ ψ ν hsd v hℓv

/-- Outputs on one fixed input that are realized by an actual Fourier-regular
test at every exponent, up to one integer spectral power. -/
def fourierRegularMonomialOutputs
    (ρ : Representation ℂ (GeneralLinear (m + 1) F.Carrier) V)
    (hρ : IsSmooth ρ)
    (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier)
    (hsd : IsSelfDual ψ ν) (v : V) : Set V :=
  {u | ∃ Φ : fourierRegularMatrixTests (m + 1) ψ ν hsd, ∃ k : ℤ, ∀ s : ℂ,
    regularMatrixZetaOperator F ρ hρ s ⟨Φ.val, Φ.property.1⟩ v =
      spectralPoint F.canonicalTopologicalData.residueCardinality s ^ k • u}

/-- Translating a realizing test realizes the translated output with the sum
of its old exponent and the determinant order of the translating element. -/
theorem representation_mem_fourierRegularMonomialOutputs
    (ρ : Representation ℂ (GeneralLinear (m + 1) F.Carrier) V)
    (hρ : IsSmooth ρ)
    (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier)
    (hsd : IsSelfDual ψ ν) (v u : V)
    (hu : u ∈ fourierRegularMonomialOutputs F ρ hρ ψ ν hsd v)
    (a : GeneralLinear (m + 1) F.Carrier) :
    ρ a u ∈ fourierRegularMonomialOutputs F ρ hρ ψ ν hsd v := by
  obtain ⟨Φ, k, hΦ⟩ := hu
  refine ⟨fourierRegularMatrixTranslate F ψ ν hsd a⁻¹ 1 Φ,
    F.canonicalTopologicalData.ord (Matrix.det a.val) + k, ?_⟩
  intro s
  change regularMatrixZetaOperator F ρ hρ s
    (regularMatrixTranslate a⁻¹ 1 ⟨Φ.val, Φ.property.1⟩) v = _
  rw [regularMatrixZetaOperator_leftTranslate, hΦ,
    normalizedDeterminantWeight_eq_spectralPoint_zpow, map_smul, smul_smul,
    zpow_add₀ (spectralPoint_ne_zero_of_pos
      (Nat.zero_lt_one.trans F.canonicalTopologicalData.residueCardinality_gt_one) s)]

/-- For a nonzero fixed input in an irreducible supercuspidal representation
of rank at least two, the monomial outputs span the whole carrier. -/
theorem span_fourierRegularMonomialOutputs_eq_top
    (hm : 0 < m)
    (ρ : Representation ℂ (GeneralLinear (m + 1) F.Carrier) V)
    (hρ : GeneralLinear.IsSupercuspidal ρ) (hi : ρ.IsIrreducible)
    (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier)
    (hsd : IsSelfDual ψ ν) (v : V) (hv : v ≠ 0) :
    Submodule.span ℂ (fourierRegularMonomialOutputs F ρ hρ.1.1 ψ ν hsd v) = ⊤ := by
  obtain ⟨Φ, u, hu, hΦ⟩ :=
    exists_fourierRegular_constant_output F hm ρ hρ ψ ν hsd v hv
  have hmem : u ∈ fourierRegularMonomialOutputs F ρ hρ.1.1 ψ ν hsd v :=
    ⟨Φ, 0, by simpa only [zpow_zero, one_smul] using hΦ⟩
  apply top_unique
  rw [← span_range_orbit_eq_top hi hu]
  apply Submodule.span_mono
  rintro _ ⟨a, rfl⟩
  exact representation_mem_fourierRegularMonomialOutputs F ρ hρ.1.1 ψ ν hsd v u hmem a

end Langlands.GodementJacquet.Padic
