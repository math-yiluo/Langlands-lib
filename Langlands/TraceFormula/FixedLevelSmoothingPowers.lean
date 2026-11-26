import Langlands.Analysis.DixmierMalliavin.Product
import Langlands.HarmonicAnalysis.SchwartzBruhatProduct
import Langlands.Representation.Hecke.NormalizedIndicator
import Langlands.TraceFormula.SplitSmoothingPowers

/-! # Positive smoothing powers at a common finite level -/

noncomputable section

namespace Langlands.TraceFormula

open Langlands.Analysis Langlands.Hecke MeasureTheory

universe u v w

section Product

variable {A : Type u} [Group A] [TopologicalSpace A] [IsTopologicalGroup A]
  [MeasurableSpace A] [BorelSpace A] [T2Space A] [LocallyCompactSpace A] [SecondCountableTopology A]
  {B : Type v} [Group B] [TopologicalSpace B] [IsTopologicalGroup B]
  [MeasurableSpace B] [BorelSpace B] [LocallyCompactSpace B] [SecondCountableTopology B]
  (μ : Measure A) [μ.IsHaarMeasure] (ν : Measure B) [ν.IsHaarMeasure]

omit [IsTopologicalGroup B] [LocallyCompactSpace B] [SecondCountableTopology B] in
private theorem integrable_smoothingPowerTensor {f : A → ℂ}
    (hf : Continuous f) (hc : HasCompactSupport f) (g : HeckeAlgebra ν) (k : ℕ) :
    Integrable (fun p : A × B => positiveConvolutionPower μ f k p.1 * g p.2) (μ.prod ν) := by
  obtain ⟨hcont, hsupp⟩ := positiveConvolutionPower_continuous_hasCompactSupport μ hf hc k
  exact (hcont.integrable_of_hasCompactSupport hsupp).mul_prod
    (HarmonicAnalysis.SchwartzBruhat.integrable (HeckeAlgebra.toTestFunction ν g) ν)

variable {H : Type w} [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]
  (π : (A × B) →* (H →L[ℂ] H)) (hn : ∀ p x, ‖π p x‖ = ‖x‖)
  (hm : ∀ x, AEStronglyMeasurable (fun p => π p x) (μ.prod ν))

/-- The integrated action of the same finite test tensored with the
`(k + 1)`-fold convolution of the infinite test. -/
def smoothingPowerTensorAction {f : A → ℂ} (hf : Continuous f) (hc : HasCompactSupport f)
    (g : HeckeAlgebra ν) (k : ℕ) : H →L[ℂ] H :=
  integratedIsometricAction (μ.prod ν) π hn hm
    (fun p => positiveConvolutionPower μ f k p.1 * g p.2)
    (integrable_smoothingPowerTensor μ ν hf hc g k)

private theorem smoothingPowerTensorAction_succ {f : A → ℂ}
    (hf : Continuous f) (hc : HasCompactSupport f)
    (K : OpenSubgroup B) (hK : IsCompact (K : Set B)) (g : HeckeAlgebra ν)
    (hg : ∀ k : K, ∀ x, g (x * k) = g x) (k : ℕ) :
    smoothingPowerTensorAction μ ν π hn hm hf hc g (k + 1) =
      smoothingPowerTensorAction μ ν π hn hm hf hc g k *
        smoothingPowerTensorAction μ ν π hn hm hf hc (HeckeAlgebra.normalizedIndicator ν K hK) 0 := by
  let e := HeckeAlgebra.normalizedIndicator ν K hK
  let a : A × B → ℂ := fun p => positiveConvolutionPower μ f k p.1 * g p.2
  let b : A × B → ℂ := fun p => positiveConvolutionPower μ f 0 p.1 * e p.2
  have hKernel : convolutionIntegral (μ.prod ν) a b =
      fun p => positiveConvolutionPower μ f (k + 1) p.1 * g p.2 := by
    funext p
    rw [show a = _ from rfl, show b = _ from rfl, convolutionIntegral_prod_tensor,
      convolutionIntegral_positiveConvolutionPower μ hf hc, Nat.add_zero]
    have hFinite : convolutionIntegral ν g e p.2 = g p.2 :=
      congrArg (fun h : HeckeAlgebra ν => h p.2)
        (HeckeAlgebra.mul_normalizedIndicator_of_rightInvariant ν K hK g hg)
    rw [hFinite]
  obtain ⟨hIntegral, hAction⟩ :=
    integratedActionConvolution (A × B) H (μ.prod ν) π hn hm a b
      (integrable_smoothingPowerTensor μ ν hf hc g k)
      (integrable_smoothingPowerTensor μ ν hf hc e 0)
  have hConv : Integrable (convolutionIntegral (μ.prod ν) a b) (μ.prod ν) := hIntegral
  change integratedIsometricAction (μ.prod ν) π hn hm
    (convolutionIntegral (μ.prod ν) a b) hConv = _ at hAction
  ext1 x
  have hx := congrArg (fun R : H →L[ℂ] H => R x) hAction
  simp only [integratedIsometricAction_apply] at hx
  rw [hKernel] at hx
  exact hx

end Product

/-- At a common right finite level, multiplying by positive powers of the
smoothing operator increases only the number of infinite convolution factors.
The same formula holds after a commuting twist. -/
def FixedLevelSmoothingPowersStatement : Prop :=
  ∀ (A : Type u) [Group A] [TopologicalSpace A] [IsTopologicalGroup A]
    [MeasurableSpace A] [BorelSpace A] [T2Space A] [LocallyCompactSpace A] [SecondCountableTopology A]
    (B : Type v) [Group B] [TopologicalSpace B] [IsTopologicalGroup B]
    [MeasurableSpace B] [BorelSpace B] [LocallyCompactSpace B] [SecondCountableTopology B]
    (μ : Measure A) [μ.IsHaarMeasure] (ν : Measure B) [ν.IsHaarMeasure]
    (H : Type w) [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]
    (π : (A × B) →* (H →L[ℂ] H)) (hn : ∀ p x, ‖π p x‖ = ‖x‖)
    (hm : ∀ x, AEStronglyMeasurable (fun p => π p x) (μ.prod ν))
    (f : A → ℂ) (hf : Continuous f) (hc : HasCompactSupport f)
    (K : OpenSubgroup B) (hK : IsCompact (K : Set B))
    (g : HeckeAlgebra ν), (∀ k : K, ∀ x, g (x * k) = g x) →
    let R := smoothingPowerTensorAction μ ν π hn hm hf hc
    let T := R (HeckeAlgebra.normalizedIndicator ν K hK) 0
    ∀ U : H →L[ℂ] H, Commute U T → ∀ k : ℕ,
      (R g 0 * U) * T ^ k = R g k * U

theorem fixedLevelSmoothingPowers : FixedLevelSmoothingPowersStatement.{u, v, w} := by
  intro A _ _ _ _ _ _ _ _ B _ _ _ _ _ _ _ μ _ ν _ H _ _ _ π hn hm
    f hf hc K hK g hg R T U hU k
  have hPow (j : ℕ) : R g 0 * T ^ j = R g j := by
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ, ← mul_assoc, ih]
      exact (smoothingPowerTensorAction_succ μ ν π hn hm hf hc K hK g hg j).symm
  rw [mul_assoc, (hU.pow_right k).eq, ← mul_assoc, hPow k]

section Transport

variable {G : Type u} [Group G] [MeasurableSpace G]
  {H : Type w} [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]
  (μ : Measure G) (π : G →* (H →L[ℂ] H)) (hn : ∀ g x, ‖π g x‖ = ‖x‖)
  (hm : ∀ x, AEStronglyMeasurable (fun g => π g x) μ)
  (f : G → ℂ) (hf : Integrable f μ)

/-- Transport the integrated action through a measure-preserving group equivalence. -/
theorem integratedIsometricAction_pullback
    {J : Type v} [Group J] [MeasurableSpace J] (ν : Measure J) (e : J ≃* G)
    (hemb : MeasurableEmbedding e) (he : MeasurePreserving e ν μ) :
    integratedIsometricAction ν (π.comp e.toMonoidHom)
        (fun g x => hn (e g) x) (fun x => (hm x).comp_measurePreserving he)
        (f ∘ e) ((he.integrable_comp_emb hemb).2 hf) =
      integratedIsometricAction μ π hn hm f hf := by
  ext1 x
  exact he.integral_comp hemb (fun g => f g • π g x)

/-- An intertwiner for a measure-preserving automorphism commutes with
the integrated action of an invariant function. -/
theorem commute_integratedIsometricAction_of_invariant
    (θ : G ≃* G) (hemb : MeasurableEmbedding θ) (hθ : MeasurePreserving θ μ μ)
    (U : H →L[ℂ] H) (hU : ∀ g x, U (π g x) = π (θ g) (U x))
    (hInv : ∀ g, f (θ g) = f g) :
    Commute U (integratedIsometricAction μ π hn hm f hf) := by
  change U * integratedIsometricAction μ π hn hm f hf =
    integratedIsometricAction μ π hn hm f hf * U
  ext1 x
  change U (∫ g, f g • π g x ∂μ) = ∫ g, f g • π g (U x) ∂μ
  rw [← U.integral_comp_comm (isometricActionIntegrand_integrable μ π hn hm f hf x)]
  calc
    _ = ∫ g, f (θ g) • π (θ g) (U x) ∂μ :=
      integral_congr_ae (Filter.Eventually.of_forall fun g => by
        change U (f g • π g x) = f (θ g) • π (θ g) (U x)
        rw [map_smul, hU, hInv])
    _ = _ := hθ.integral_comp hemb (fun g => f g • π g (U x))

end Transport

end Langlands.TraceFormula
