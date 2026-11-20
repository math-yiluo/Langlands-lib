import Langlands.Representation.Archimedean.RealHilbertDualCompact
import Langlands.Representation.Archimedean.RealContragredientProof
import Langlands.Representation.Archimedean.SmoothHilbertExponential
import Langlands.Representation.Archimedean.TransposeTwist

/-! # The real algebraic pairing from invariant Hilbert character traces -/

noncomputable section

open MeasureTheory
open scoped Manifold ContDiff TensorProduct Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean

open DerivativeSmoothVectors (derivativeCLM representation operator toSmooth smoothedOperator)
open Langlands.Analysis.OperatorIdeals (IsTraceClass operatorTrace)
open Langlands.HarmonicAnalysis.Distribution (transposeHomeomorph)
open Langlands.KFiniteDual (kDual kDualRep)

attribute [local instance 100] LieRing.ofAssociativeRing

variable (n : ℕ)

local notation "GLR" => Langlands.GeneralLinear n ℝ
local notation "K" => Matrix.unitaryGroup (Fin n) ℝ
local notation "Kc" => unitaryCompact ℝ n
local notation "Mat" => Matrix (Fin n) (Fin n) ℝ
local notation "𝔤" => ℂ ⊗[ℝ] Mat
local notation "I" => matrixModel ℝ n
local notation "θ" => Langlands.GeneralLinear.inverseTranspose n ℝ

private theorem inv_inverseTranspose_generalLinearRealExp (X : Mat) (t : ℝ) :
    (θ (generalLinearRealExp ℝ n X t))⁻¹ = generalLinearRealExp ℝ n X.transpose t := by
  apply Units.ext
  change (NormedSpace.exp (t • X)).transpose = NormedSpace.exp (t • X.transpose)
  rw [← Matrix.exp_transpose, Matrix.transpose_smul]

section Algebraic

variable {V : Type*} [AddCommGroup V] [Module ℂ V]
  (ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℝ) V)
  (π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) →ₗ⁅ℂ⁆ Module.End ℂ V)
  (hgk : IsRealGKModule n ρ π)

local notation "σ" => transposeTwistRep ℝ n (kDualRep ρ)
local notation "τ" => transposeTwistLie ℝ n (RealContragredient.dualLie hgk)

private theorem transposeTwist_kDualRep_apply_apply (k : K) (w : kDual ρ) (v : V) :
    ((σ k w : kDual ρ) : Module.Dual ℂ V) v = (w : Module.Dual ℂ V) (ρ k⁻¹ v) := by
  rw [transposeTwistRep_apply, compactIota_real, Langlands.KFiniteDual.coe_kDualRep_apply,
    Langlands.KFiniteDual.dual_apply_apply]

private theorem transposeTwist_dualLie_one_tmul_apply_apply (X : Mat) (w : kDual ρ) (v : V) :
    ((τ (1 ⊗ₜ[ℝ] X) w : kDual ρ) : Module.Dual ℂ V) v =
      (w : Module.Dual ℂ V) (π (1 ⊗ₜ[ℝ] X.transpose) v) := by
  rw [transposeTwistLie_apply, complexifiedMatrixLieIota_tmul, RealContragredient.dualLie_apply_apply,
    TensorProduct.tmul_neg, map_neg, LinearMap.neg_apply, map_neg, neg_neg]

/-- Evaluating an equivalence with the inverse-transpose twist of the finite dual
gives the required nonzero bilinear pairing. -/
theorem hasNonzeroTransposeGKPairing_of_equiv_to_twisted_dual [Nontrivial V]
    (a : V ≃ₗ[ℂ] kDual ρ)
    (haK : ∀ (k : K) (v : V), a (ρ k v) = σ k (a v))
    (haL : ∀ (X : 𝔤) (v : V), a (π X v) = τ X (a v)) :
    HasNonzeroTransposeGKPairing ℝ n ρ π := by
  let B := ((kDual ρ).subtype.comp a.toLinearMap).flip
  refine ⟨B, ⟨?_, ?_⟩, ?_⟩
  · intro k y x
    change (a (ρ (compactIota ℝ n k) x) : Module.Dual ℂ V) (ρ k y) =
      (a x : Module.Dual ℂ V) y
    rw [compactIota_real, haK, transposeTwist_kDualRep_apply_apply n ρ,
      ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  · intro X y x
    change (a x : Module.Dual ℂ V) (π X y) +
      (a (π (complexifiedMatrixLieIota ℝ n X) x) : Module.Dual ℂ V) y = 0
    rw [haL, transposeTwistLie_apply, complexifiedMatrixLieIota_involutive,
      RealContragredient.dualLie_apply_apply, add_neg_cancel]
  · intro hB
    obtain ⟨x, hx⟩ := exists_ne (0 : V)
    apply hx
    apply a.injective
    rw [map_zero]
    apply Subtype.ext
    apply LinearMap.ext
    intro y
    exact LinearMap.congr_fun (LinearMap.congr_fun hB y) x

section Comparison

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (R : Langlands.GeneralLinear n ℝ →* (H →L[ℂ] H))
  (e : V →ₗ[ℂ] DerivativeSmoothVectors (matrixModel ℝ n) R)

local notation "S" => inverseTransposeContinuousDual ℝ n R
local notation "ε" => derivativeCLM I R []
local notation "η" => derivativeCLM I S []
local notation "g" => LinearMap.comp (ContinuousLinearMap.toLinearMap ε) e

/-- Restriction of the twisted smooth continuous dual agrees with the compact
and genuine derived actions on the twisted algebraic finite dual. -/
theorem smoothHilbertDual_action_comparison
    (f : kDual ρ →ₗ[ℂ] DerivativeSmoothVectors I S)
    (hden : DenseRange g) (hf : ∀ (w : kDual ρ) (v : V), η (f w) (g v) = (w : Module.Dual ℂ V) v)
    (hk : ∀ (k : K) (v : V), e (ρ k v) = representation I R (Unitary.toUnits k) (e v))
    (hX : ∀ (X : Mat) (v : V), e (π (1 ⊗ₜ[ℝ] X) v) = operator I R X (e v)) :
    (∀ (k : K) (w : kDual ρ), f (σ k w) = representation I S (Unitary.toUnits k) (f w)) ∧
    ∀ (X : Mat) (w : kDual ρ), f (τ (1 ⊗ₜ[ℝ] X) w) = operator I S X (f w) := by
  have hinj : Function.Injective ((restrictHilbertFunctional g).comp (η).toLinearMap) :=
    (restrictHilbertFunctional_injective g hden).comp
      (fun _ _ h => (toSmooth I S).injective (Subtype.ext h))
  constructor
  · intro k w
    apply hinj
    apply LinearMap.ext
    intro v
    change η (f (σ k w)) (g v) = S (Unitary.toUnits k) (η (f w)) (g v)
    rw [hf, transposeTwist_kDualRep_apply_apply n ρ, inverseTransposeContinuousDual_realCompact_apply]
    have h : g (ρ k⁻¹ v) = R (Unitary.toUnits k⁻¹) (g v) := by
      change ε (e (ρ k⁻¹ v)) = _
      rw [hk]
      rfl
    rw [← h, hf]
  · intro X w
    apply hinj
    apply LinearMap.ext
    intro v
    let L := (ContinuousLinearMap.apply ℂ ℂ (g v)).comp (η)
    let M := (η (f w)).comp (ε)
    have hS := hasSmoothHilbertExponentialDerivatives ℝ n S X (f w) L
    have hR := hasSmoothHilbertExponentialDerivatives ℝ n R X.transpose (e v) M
    have heq :
        (fun t : ℝ => L (representation I S (generalLinearRealExp ℝ n X t) (f w))) =
          fun t : ℝ => M (representation I R (generalLinearRealExp ℝ n X.transpose t) (e v)) := by
      funext t
      change (continuousDualRepresentation R (θ (generalLinearRealExp ℝ n X t)) (η (f w))) (g v) =
        η (f w) (R (generalLinearRealExp ℝ n X.transpose t) (g v))
      rw [continuousDualRepresentation_apply, inv_inverseTranspose_generalLinearRealExp n]
    rw [heq] at hS
    have h := hS.unique hR
    change η (operator I S X (f w)) (g v) = η (f w) (ε (operator I R X.transpose (e v))) at h
    rw [← hX X.transpose v] at h
    change η (operator I S X (f w)) (g v) = η (f w) (g (π (1 ⊗ₜ[ℝ] X.transpose) v)) at h
    change η (f (τ (1 ⊗ₜ[ℝ] X) w)) (g v) = η (operator I S X (f w)) (g v)
    rw [hf, transposeTwist_dualLie_one_tmul_apply_apply n ρ π hgk, h, hf]

end Comparison

end Algebraic

section Character

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (R : Langlands.GeneralLinear n ℝ →* (H →L[ℂ] H)) (hR : IsContinuousRepresentation R)
  [MeasurableSpace (Langlands.GeneralLinear n ℝ)] [BorelSpace (Langlands.GeneralLinear n ℝ)]
  (μ : Measure (Langlands.GeneralLinear n ℝ)) [μ.IsHaarMeasure]

/-- The smooth kernel trace is invariant under ordinary transpose and is supplied
by trace-class operators on the transposed tests. -/
def HasTransposeInvariantSmoothKernelTrace : Prop :=
  ∀ (κ : GLR → ℂ) (hκ : ContMDiff I 𝓘(ℝ, ℂ) ∞ κ) (hkc : HasCompactSupport κ),
    let T := smoothedOperator R μ hR (κ ∘ transposeHomeomorph n ℝ)
      (hκ.continuous.comp (transposeHomeomorph n ℝ).continuous)
      (hkc.comp_homeomorph (transposeHomeomorph n ℝ))
    IsTraceClass T ∧ operatorTrace T = operatorTrace (smoothedOperator R μ hR κ hκ.continuous hkc)

variable [μ.Regular]

theorem sameSmoothKernelTrace_inverseTransposeContinuousDual
    (h : HasTransposeInvariantSmoothKernelTrace n R hR μ) :
    SameSmoothKernelTrace ℝ n μ R (inverseTransposeContinuousDual ℝ n R) hR
      (isContinuousRepresentation_inverseTransposeContinuousDual ℝ n R hR) := by
  intro κ hκ hkc
  obtain ⟨htr, heq⟩ := h κ hκ hkc
  have hc := traceClass_and_trace_inverseTransposeContinuousDual ℝ n R μ hR κ hκ.continuous hkc htr
  exact heq.symm.trans hc.2.symm

end Character

section Pairing

variable [MeasurableSpace (Langlands.GeneralLinear n ℝ)] [BorelSpace (Langlands.GeneralLinear n ℝ)]
  (μ : Measure (Langlands.GeneralLinear n ℝ)) [μ.IsHaarMeasure] [μ.Regular] [μ.IsMulRightInvariant]
  [MeasurableSpace (unitaryCompact ℝ n)] [BorelSpace (unitaryCompact ℝ n)]
  (ν : Measure (unitaryCompact ℝ n)) [ν.IsHaarMeasure] [ν.IsInvInvariant] [IsProbabilityMeasure ν]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (R : Langlands.GeneralLinear n ℝ →* (H →L[ℂ] H))
  {V : Type*} [AddCommGroup V] [Module ℂ V]
  (ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℝ) V)
  (π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) →ₗ⁅ℂ⁆ Module.End ℂ V)
  (e : V ≃ₗ[ℂ] smoothHilbertKFinite ℝ n R)

local notation "S" => inverseTransposeContinuousDual ℝ n R
local notation "ε" => derivativeCLM I R []

include ν in
/-- A compatible real Hilbert globalization with unitary compact restriction and
transpose invariant trace-class kernel traces yields the original algebraic pairing. -/
theorem hasRealTransposePairing_of_smoothKernelTrace
    (hgk : IsRealGKModule n ρ π) (hirr : IsIrreducibleGKModule ρ π)
    (hadm : IsAdmissibleGKModule ρ) (hG : IsSmoothHilbertGlobalization ℝ n R ρ π e)
    (hU : HasUnitaryRealCompactAction n R)
    (ht : HasTransposeInvariantSmoothKernelTrace n R hG.1.1 μ) :
    HasNonzeroTransposeGKPairing ℝ n ρ π := by
  let : Nontrivial V := hirr.1
  let E := smoothHilbertGlobalizationMap ℝ n R e
  let g := (ε).toLinearMap.comp E
  have hε : DenseRange ε :=
    (dense_smoothVectors_units R μ hG.1.1).denseRange_val.comp
      (toSmooth I R).surjective.denseRange continuous_subtype_val
  have hd : DenseRange g := hε.comp hG.2.1 (ε).continuous
  have hi : Function.Injective g := by
    intro x y hxy
    apply e.injective
    apply Subtype.ext
    exact (toSmooth I R).injective (Subtype.ext hxy)
  have hk (k : K) (v : V) : g (ρ k v) = R (Unitary.toUnits k) (g v) := by
    change ε (E (ρ k v)) = _
    rw [hG.2.2.1]
    rfl
  let a := smoothHilbertDualEquiv n R ρ g hk μ ν hG.1.1 hd hi hgk.1 hgk.2.1 hadm hU
  let f := a.symm
  let F := smoothHilbertGlobalizationMap ℝ n S f
  have heval (w : kDual ρ) (v : V) : derivativeCLM I S [] (F w) (g v) =
      (w : Module.Dual ℂ V) v :=
    congrArg (fun L : kDual ρ => (L : Module.Dual ℂ V) v) (a.apply_symm_apply w)
  let σ := transposeTwistRep ℝ n (kDualRep ρ)
  let τ := transposeTwistLie ℝ n (RealContragredient.dualLie hgk)
  have hS := isContinuousRepresentation_inverseTransposeContinuousDual ℝ n R hG.1.1
  have hadmS := isAdmissible_inverseTransposeContinuousDual n R ρ g hk hd hgk.1 hgk.2.1 hadm
  have hirrS : IsIrreducibleGKModule σ τ :=
    isIrreducibleGKModule_transposeTwist ℝ n _ _ (RealContragredient.isIrreducible_kDual hgk hirr hadm)
  have hcmp := smoothHilbertDual_action_comparison n ρ π hgk R E F hd heval hG.2.2.1 hG.2.2.2.1
  have ht' := sameSmoothKernelTrace_inverseTransposeContinuousDual n R hG.1.1 μ ht
  obtain ⟨b, hbK, hbL⟩ := exists_real_gkEquiv_of_sameSmoothKernelTrace n μ ν R S ρ π σ τ e f
    hG.1.1 hS hG.1.2.2 hadmS hG.2.2.1 hcmp.1 hG.2.2.2.1 hcmp.2 hG.2.2.2.2
    (hasSmoothHilbertExponentialDerivatives ℝ n S) hgk hirr hirrS hU ht'
  exact hasNonzeroTransposeGKPairing_of_equiv_to_twisted_dual n ρ π hgk b hbK hbL

end Pairing

end Langlands.Archimedean
