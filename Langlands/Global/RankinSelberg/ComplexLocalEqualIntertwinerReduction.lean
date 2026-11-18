import Langlands.Global.RankinSelberg.ComplexLocalEqualHolomorphy

/-! # Reduction of the complex equal-rank equation to individual intertwiner images -/

noncomputable section

open MeasureTheory Langlands.LocalFactor.Archimedean
open Langlands.Automorphic

set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

open ArchimedeanLocal

private def kernelEquation {Q : Type*} [MeasurableSpace Q] (μ : Measure Q)
    (K Kd : ℂ → Q → ℂ) (L R : ℂ → ℂ) : Prop :=
  ∃ (σ : ℝ) (M Md : ℂ → ℂ),
    (∀ s : ℂ, σ < s.re → Integrable (K s) μ) ∧
    (∀ s : ℂ, σ < s.re → Integrable (Kd s) μ) ∧
    MeromorphicOn M Set.univ ∧ MeromorphicOn Md Set.univ ∧
    (∀ s : ℂ, σ < s.re → (∫ q, K s q ∂μ) = M s) ∧
    (∀ s : ℂ, σ < s.re → (∫ q, Kd s q ∂μ) = Md s) ∧
    ∀ᶠ s in Filter.codiscrete ℂ, L s * Md (1 - s) = R s * M s

private theorem kernelEquation_zero {Q : Type*} [MeasurableSpace Q] (μ : Measure Q)
    (L R : ℂ → ℂ) : kernelEquation μ 0 0 L R := by
  have hz : MeromorphicOn (0 : ℂ → ℂ) Set.univ := fun z _ => MeromorphicAt.const 0 z
  refine ⟨0, 0, 0, ?_, ?_, hz, hz, ?_, ?_, ?_⟩
  · intro s _
    exact integrable_zero _ _ _
  · intro s _
    exact integrable_zero _ _ _
  · intros
    simp
  · intros
    simp
  · exact Filter.Eventually.of_forall (by simp)

private theorem kernelEquation_add {Q : Type*} [MeasurableSpace Q] {μ : Measure Q}
    {K₁ K₂ Kd₁ Kd₂ : ℂ → Q → ℂ} {L R : ℂ → ℂ}
    (h₁ : kernelEquation μ K₁ Kd₁ L R) (h₂ : kernelEquation μ K₂ Kd₂ L R) :
    kernelEquation μ (K₁ + K₂) (Kd₁ + Kd₂) L R := by
  obtain ⟨σ₁, M₁, Md₁, hK₁, hKd₁, hM₁, hMd₁, hEq₁, hEqd₁, hFe₁⟩ := h₁
  obtain ⟨σ₂, M₂, Md₂, hK₂, hKd₂, hM₂, hMd₂, hEq₂, hEqd₂, hFe₂⟩ := h₂
  have hσ₁ {s : ℂ} (hs : max σ₁ σ₂ < s.re) : σ₁ < s.re :=
    (le_max_left σ₁ σ₂).trans_lt hs
  have hσ₂ {s : ℂ} (hs : max σ₁ σ₂ < s.re) : σ₂ < s.re :=
    (le_max_right σ₁ σ₂).trans_lt hs
  refine ⟨max σ₁ σ₂, M₁ + M₂, Md₁ + Md₂,
    fun s hs => (hK₁ s (hσ₁ hs)).add (hK₂ s (hσ₂ hs)),
    fun s hs => (hKd₁ s (hσ₁ hs)).add (hKd₂ s (hσ₂ hs)),
    fun z hz => (hM₁ z hz).add (hM₂ z hz), fun z hz => (hMd₁ z hz).add (hMd₂ z hz),
    ?_, ?_, ?_⟩
  · intro s hs
    simp only [Pi.add_apply, integral_add (hK₁ s (hσ₁ hs)) (hK₂ s (hσ₂ hs)),
      hEq₁ s (hσ₁ hs), hEq₂ s (hσ₂ hs)]
  · intro s hs
    simp only [Pi.add_apply, integral_add (hKd₁ s (hσ₁ hs)) (hKd₂ s (hσ₂ hs)),
      hEqd₁ s (hσ₁ hs), hEqd₂ s (hσ₂ hs)]
  · filter_upwards [hFe₁, hFe₂] with s hs₁ hs₂
    simp only [Pi.add_apply, mul_add, hs₁, hs₂]

attribute [local instance] archimedeanEquationComplexGLMeasurable
  archimedeanEquationComplexGLBorel archimedeanEquationComplexNMeasurable
  archimedeanEquationComplexNBorel archimedeanEquationComplexQMeasurable
  archimedeanEquationComplexQBorel

/-- For a fixed pair, convergence, meromorphic continuation and the codiscrete equation
with the exact local factors. The two holomorphy clauses follow from convergence. -/
def ComplexLocalEqualPairStatement {r : ℕ} (d d' : List ComplexCharacterData)
    (a : ℂˣ) (D : ComplexQuotientMeasureData r)
    (W W' : Langlands.GeneralLinear (r + 1) ℂ → ℂ)
    (Φ : SchwartzMap (Fin (r + 1) → ℂ) ℂ) : Prop :=
  kernelEquation D.measure (complexEqualIntegrand W W' Φ)
    (complexEqualIntegrand (ArchimedeanLocal.dualFunction (r + 1) W)
      (ArchimedeanLocal.dualFunction (r + 1) W')
      (complexFourierTransform a Φ))
    (fun s => ((complexPairLFactor d d').denominator s)⁻¹)
    (fun s => complexCentralSign d' ^ r *
      (complexPairEpsilon d d' a ‖(a : ℂ)‖₊ (nnnorm_pos.mpr a.ne_zero) s : ℂ) *
      ((complexPairLFactor (d.map ComplexCharacterData.inv)
        (d'.map ComplexCharacterData.inv)).denominator (1 - s))⁻¹)

section FixedData

variable {r : ℕ} {d d' : List ComplexCharacterData} {a : ℂˣ} {D : ComplexQuotientMeasureData r}
  {Φ : SchwartzMap (Fin (r + 1) → ℂ) ℂ}
  {W W₁ W₂ W' W'₁ W'₂ : Langlands.GeneralLinear (r + 1) ℂ → ℂ}

private theorem pair_zero_left : ComplexLocalEqualPairStatement d d' a D 0 W' Φ := by
  unfold ComplexLocalEqualPairStatement
  convert kernelEquation_zero D.measure _ _ using 1 <;> funext s q <;>
    simp [complexEqualIntegrand, equalIntegrand, ArchimedeanLocal.dualFunction]

private theorem pair_zero_right : ComplexLocalEqualPairStatement d d' a D W 0 Φ := by
  unfold ComplexLocalEqualPairStatement
  convert kernelEquation_zero D.measure _ _ using 1 <;> funext s q <;>
    simp [complexEqualIntegrand, equalIntegrand, ArchimedeanLocal.dualFunction]

private theorem pair_add_left
    (h₁ : ComplexLocalEqualPairStatement d d' a D W₁ W' Φ)
    (h₂ : ComplexLocalEqualPairStatement d d' a D W₂ W' Φ) :
    ComplexLocalEqualPairStatement d d' a D (W₁ + W₂) W' Φ := by
  unfold ComplexLocalEqualPairStatement
  convert kernelEquation_add h₁ h₂ using 1 <;> funext s q <;>
    simp [complexEqualIntegrand, equalIntegrand, ArchimedeanLocal.dualFunction, add_mul]

private theorem pair_add_right
    (h₁ : ComplexLocalEqualPairStatement d d' a D W W'₁ Φ)
    (h₂ : ComplexLocalEqualPairStatement d d' a D W W'₂ Φ) :
    ComplexLocalEqualPairStatement d d' a D W (W'₁ + W'₂) Φ := by
  unfold ComplexLocalEqualPairStatement
  convert kernelEquation_add h₁ h₂ using 1 <;> funext s q <;>
    simp [complexEqualIntegrand, equalIntegrand, ArchimedeanLocal.dualFunction, mul_add, add_mul]

end FixedData

/-- Extend an additive predicate on individual intertwiner values to their model. -/
private theorem complexWhittakerModel_induction {r : ℕ} {d : List ComplexCharacterData}
    {a : ℂˣ} {W : Langlands.GeneralLinear (r + 1) ℂ → ℂ}
    {P : (Langlands.GeneralLinear (r + 1) ℂ → ℂ) → Prop}
    (hW : W ∈ complexWhittakerModel r d a)
    (h0 : P 0) (hadd : ∀ x y, P x → P y → P (x + y))
    (himage : ∀ B, IsComplexWhittakerIntertwiner r d a B → ∀ f, P (B f)) : P W := by
  unfold complexWhittakerModel at hW
  refine Submodule.iSup_induction _ hW (motive := P) ?_ h0 hadd
  intro B V hV
  refine Submodule.iSup_induction _ hV (motive := P) ?_ h0 hadd
  rintro hB _ ⟨f, rfl⟩
  exact himage B hB f

/-- The open analytic premise for pairs of values of individual Whittaker intertwiners. -/
def ComplexLocalEqualIntertwinerPairStatement : Prop :=
  ∀ (r : ℕ) (d d' : List ComplexCharacterData), d.length = r + 1 → d'.length = r + 1 →
  ∀ (a : ℂˣ) (D : ComplexQuotientMeasureData r)
    (B : complexStandardKFinite (r + 1) d →ₗ[ℂ] (Langlands.GeneralLinear (r + 1) ℂ → ℂ))
    (B' : complexStandardKFinite (r + 1) d' →ₗ[ℂ] (Langlands.GeneralLinear (r + 1) ℂ → ℂ)),
    IsComplexWhittakerIntertwiner r d a B →
    IsComplexWhittakerIntertwiner r d' (-a) B' →
  ∀ (f : complexStandardKFinite (r + 1) d) (f' : complexStandardKFinite (r + 1) d')
    (Φ : SchwartzMap (Fin (r + 1) → ℂ) ℂ),
    ComplexLocalEqualPairStatement d d' a D (B f) (B' f') Φ

/-- The image-pair analytic premise implies the exact local equal-rank statement. -/
def ComplexLocalEqualIntertwinerReductionStatement : Prop :=
  ComplexLocalEqualIntertwinerPairStatement → ComplexLocalEqualFunctionalEquationStatement

theorem complexLocalEqualIntertwinerReduction : ComplexLocalEqualIntertwinerReductionStatement := by
  intro h r d d' hd hd' a D W W' Φ hW hW'
  have hPair : ComplexLocalEqualPairStatement d d' a D W W' Φ := by
    refine complexWhittakerModel_induction hW (P := fun V =>
      ComplexLocalEqualPairStatement d d' a D V W' Φ) pair_zero_left
        (fun _ _ => pair_add_left) ?_
    intro B hB f
    refine complexWhittakerModel_induction hW' (P := fun V' =>
      ComplexLocalEqualPairStatement d d' a D (B f) V' Φ) pair_zero_right
        (fun _ _ => pair_add_right) ?_
    intro B' hB' f'
    exact h r d d' hd hd' a D B B' hB hB' f f' Φ
  obtain ⟨σ, M, Md, hK, hKd, hM, hMd, hEq, hEqd, hFe⟩ := hPair
  have hOpen : IsOpen {s : ℂ | σ < s.re} := isOpen_lt continuous_const Complex.continuous_re
  exact ⟨σ, M, Md, hK, hKd, differentiableOn_complexEqualIntegral D W W' Φ hOpen hK,
    differentiableOn_complexEqualIntegral D (ArchimedeanLocal.dualFunction (r + 1) W)
      (ArchimedeanLocal.dualFunction (r + 1) W')
      (complexFourierTransform a Φ) hOpen hKd, hM, hMd, hEq, hEqd, hFe⟩

end Langlands.Global.RankinSelbergGlobal
