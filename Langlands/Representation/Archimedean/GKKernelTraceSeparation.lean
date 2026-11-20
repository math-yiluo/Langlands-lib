import Langlands.Representation.Archimedean.GKOrbitTraceSeparation
import Langlands.Representation.Archimedean.HilbertCompressedTrace

/-! # Algebraic separation by smooth kernel traces -/

noncomputable section

open MeasureTheory
open scoped Manifold ContDiff TensorProduct Matrix.Norms.Operator InnerProductSpace

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean

open DerivativeSmoothVectors (derivativeCLM smoothedOperator)
open Langlands.Analysis.OperatorIdeals (operatorTrace)

attribute [local instance 100] LieRing.ofAssociativeRing

variable (F : Type) [RCLike F] (n : ℕ)

local notation "GLF" => Langlands.GeneralLinear n F
local notation "K" => Matrix.unitaryGroup (Fin n) F
local notation "Mat" => Matrix (Fin n) (Fin n) F
local notation "𝔤" => ℂ ⊗[ℝ] Mat
local notation "I" => matrixModel F n

variable [MeasurableSpace (Langlands.GeneralLinear n F)] [BorelSpace (Langlands.GeneralLinear n F)]
  (μ : Measure (Langlands.GeneralLinear n F)) [IsFiniteMeasureOnCompacts μ]
  {H J : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup J] [InnerProductSpace ℂ J] [CompleteSpace J]
  (R : Langlands.GeneralLinear n F →* (H →L[ℂ] H))
  (S : Langlands.GeneralLinear n F →* (J →L[ℂ] J))
  (hR : IsContinuousRepresentation R) (hS : IsContinuousRepresentation S)

/-- The two Hilbert actions have equal trace values on every smooth compact inverse kernel. -/
def SameSmoothKernelTrace : Prop :=
  ∀ (κ : GLF → ℂ) (hκ : ContMDiff I 𝓘(ℝ, ℂ) ∞ κ) (hkc : HasCompactSupport κ),
    operatorTrace (smoothedOperator R μ hR κ hκ.continuous hkc) =
      operatorTrace (smoothedOperator S μ hS κ hκ.continuous hkc)

variable [μ.IsMulRightInvariant] [μ.IsOpenPosMeasure]
  {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
  (ν : Measure X) [IsFiniteMeasure ν] (j : C(X, Langlands.GeneralLinear n F)) (a : C(X, ℂ))
  {P Q : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
  [FiniteDimensional ℂ P] [NormedAddCommGroup Q] [InnerProductSpace ℂ Q] [CompleteSpace Q]
  [FiniteDimensional ℂ Q]
  (i : P →L[ℂ] H) (p : H →L[ℂ] P) (k : Q →L[ℂ] J) (q : J →L[ℂ] Q)
  {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  (e : V →ₗ[ℂ] DerivativeSmoothVectors (matrixModel F n) R)
  (f : W →ₗ[ℂ] DerivativeSmoothVectors (matrixModel F n) S)
  (ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) F) V)
  (π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) F) →ₗ⁅ℂ⁆ Module.End ℂ V)
  (σ : Representation ℂ (Matrix.unitaryGroup (Fin n) F) W)
  (τ : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) F) →ₗ⁅ℂ⁆ Module.End ℂ W)

local notation "ε" => derivativeCLM I R []
local notation "η" => derivativeCLM I S []

/-- A common finite compact average converts agreement of smooth kernel traces to an
equivalence of the compatible irreducible algebraic modules. Its inserted vectors must
come from those modules, and its first compressed identity trace must be nonzero. -/
theorem exists_gkEquiv_of_sameSmoothKernelTrace
    (hirrR : IsIrreducibleGKModule ρ π) (hirrS : IsIrreducibleGKModule σ τ)
    (hkR : ∀ (l : K) (v : V), e (ρ l v) =
      DerivativeSmoothVectors.representation I R (Unitary.toUnits l) (e v))
    (hkS : ∀ (l : K) (w : W), f (σ l w) =
      DerivativeSmoothVectors.representation I S (Unitary.toUnits l) (f w))
    (hXR : ∀ (Y : Mat) (v : V), e (π (1 ⊗ₜ[ℝ] Y) v) = DerivativeSmoothVectors.operator I R Y (e v))
    (hXS : ∀ (Y : Mat) (w : W), f (τ (1 ⊗ₜ[ℝ] Y) w) = DerivativeSmoothVectors.operator I S Y (f w))
    (hExpR : HasSmoothHilbertExponentialDerivatives F n R)
    (hExpS : HasSmoothHilbertExponentialDerivatives F n S)
    (hi : Set.range i ⊆ Set.range (fun v => ε (e v)))
    (hk : Set.range k ⊆ Set.range (fun w => η (f w)))
    (hPR : ∀ v : H, i (p v) = ∫ x, a x • R (j x) v ∂ν)
    (hPS : ∀ w : J, k (q w) = ∫ x, a x • S (j x) w ∂ν)
    (hn : hilbertCompressionTrace R i p 1 ≠ 0)
    (htrace : SameSmoothKernelTrace F n μ R S hR hS) :
    ∃ b : V ≃ₗ[ℂ] W, (∀ (l : K) (v : V), b (ρ l v) = σ l (b v)) ∧
      ∀ (Y : 𝔤) (v : V), b (π Y v) = τ Y (b v) := by
  let bP := stdOrthonormalBasis ℂ P
  let bQ := stdOrthonormalBasis ℂ Q
  have hv (d : Fin (Module.finrank ℂ P)) : ∃ v : V, ε (e v) = i (bP d) :=
    hi ⟨bP d, rfl⟩
  have hw (d : Fin (Module.finrank ℂ Q)) : ∃ w : W, η (f w) = k (bQ d) :=
    hk ⟨bQ d, rfl⟩
  choose v hv using hv
  choose w hw using hw
  let ℓ := fun d => (innerSL ℂ (bP d)).comp p
  let m := fun d => (innerSL ℂ (bQ d)).comp q
  have heR : orbitCoefficientProfile F n R e ℓ v = hilbertCompressionTrace R i p := by
    funext g
    simp only [orbitCoefficientProfile_apply, hilbertCompressionTrace_eq_sum R i p g bP,
      hv, ℓ, ContinuousLinearMap.comp_apply, innerSL_apply_apply]
  have heS : orbitCoefficientProfile F n S f m w = hilbertCompressionTrace S k q := by
    funext g
    simp only [orbitCoefficientProfile_apply, hilbertCompressionTrace_eq_sum S k q g bQ,
      hw, m, ContinuousLinearMap.comp_apply, innerSL_apply_apply]
  apply exists_gkEquiv_of_orbitCoefficientProfile_eq F n R S e f ρ π σ τ ℓ m hirrR hirrS
    hkR hkS hXR hXS hExpR hExpS v w
  · rwa [heR]
  · rw [heR, heS]
    exact hilbertCompressionTrace_eq_of_kernelTrace_eq μ ν j a R S i p k q hR hS hPR hPS htrace

end Langlands.Archimedean
