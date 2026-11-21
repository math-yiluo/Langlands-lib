import Langlands.Global.RankinSelberg.RealWhittakerWeightedVectors
import Langlands.Representation.Archimedean.SmoothCasselmanWallachStatement

/-! # Genuine Banach smooth vectors for uniform real Whittaker intertwiners -/

noncomputable section

open Langlands.Archimedean Langlands.GeneralLinear Langlands.LocalFactor.Archimedean
open scoped Manifold ContDiff Matrix.Norms.Operator ZeroAtInfty TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealWhittakerBanachModel

open RealWhittakerWeightedVectors RealPlaceRestriction

variable {r : ℕ}

local notation "G" => Langlands.GeneralLinear (r + 1) ℝ
local notation "M" => Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ
local notation "K" => Matrix.unitaryGroup (Fin (r + 1)) ℝ
local notation "E" => (Langlands.GeneralLinear (r + 1) ℝ →C₀ ℂ)
local notation "𝓘G" => matrixModel ℝ (r + 1)
local notation "ρ" d => HeightWeightedRightTranslation.representation (A := M) d
local notation "V" ds => Automorphic.realStandardKFinite (r + 1) ds

private theorem hasHeightDerivativeBound_of_uniform {ds : List RealBlock} {a : ℝˣ}
    {B : (V ds) →ₗ[ℂ] (G → ℂ)} (hB : IsRealWhittakerIntertwiner r ds a B) {N : ℕ}
    (hN : ∀ f : V ds, ∃ C : ℝ, 0 ≤ C ∧ ∀ g, ‖B f g‖ ≤ C * realMatrixHeight g ^ N)
    (f : V ds) : HasHeightDerivativeBound r (2 * N) (B f) := by
  refine ⟨hB.2.1 f, fun Xs => ?_⟩
  obtain ⟨f', he⟩ := RealUniformWhittaker.exists_iteratedRightDerivative_eq_coefficient hB f Xs
  obtain ⟨C, hC, hBound⟩ := hN f'
  let A : ℝ := 2 * ((r + 1 : ℕ) : ℝ) ^ 2
  refine ⟨C * A ^ N, by dsimp [A]; positivity, fun g => ?_⟩
  rw [he]
  calc
    _ ≤ C * realMatrixHeight g ^ N := hBound g
    _ ≤ C * (A * Archimedean.unitHeight g ^ 2) ^ N :=
      mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (realMatrixHeight_nonneg g) (realMatrixHeight_le_unitHeight_sq g) _) hC
    _ = _ := by rw [mul_pow, ← pow_mul, mul_assoc]

private def pointEval (x : G) : E →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun v => v x
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    1 (fun v => by
      change ‖v.toBCF x‖ ≤ 1 * ‖v.toBCF‖
      rw [one_mul]
      exact v.toBCF.norm_coe_le_norm x)

/-- Evaluation at the identity after undoing the height weight. -/
def evaluation (d : ℕ) : DerivativeSmoothVectors 𝓘G (ρ d) →L[ℂ] ℂ :=
  ((Archimedean.unitHeight (1 : G) ^ d : ℝ) : ℂ) •
    (pointEval (1 : G)).comp (DerivativeSmoothVectors.derivativeCLM 𝓘G (ρ d) [])

private theorem evaluation_apply (d : ℕ) (v : DerivativeSmoothVectors 𝓘G (ρ d)) :
    evaluation d v = Archimedean.unitHeight (1 : G) ^ d •
      (DerivativeSmoothVectors.toSmooth 𝓘G (ρ d) v).val 1 := by
  rw [evaluation, smul_apply, ContinuousLinearMap.comp_apply,
    DerivativeSmoothVectors.derivativeCLM_apply, iteratedLieDerivative_nil]
  rfl

/-- Any uniform coefficient intertwiner lifts to a genuine smooth Banach carrier.
The evaluation there recovers its coefficient after every actual right translation. -/
def RealWhittakerBanachModelStatement : Prop :=
  ∀ (r : ℕ) (ds : List RealBlock) (a : ℝˣ)
    (B : Automorphic.realStandardKFinite (r + 1) ds →ₗ[ℂ]
      (Langlands.GeneralLinear (r + 1) ℝ → ℂ)),
    IsRealUniformWhittakerIntertwiner r ds a B →
    ∃ d : ℕ,
      let R₀ := HeightWeightedRightTranslation.representation
        (A := Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ) d
      ∃ J : Automorphic.realStandardKFinite (r + 1) ds →ₗ[ℂ]
          DerivativeSmoothVectors (matrixModel ℝ (r + 1)) R₀,
        IsSmoothGKIntertwiner ℝ (r + 1) R₀ (realStandardRep (r + 1) ds) (realStandardLie (r + 1) ds) J ∧
        ∀ f g, evaluation d (DerivativeSmoothVectors.representation (matrixModel ℝ (r + 1)) R₀ g (J f)) = B f g

theorem realWhittakerBanachModel : RealWhittakerBanachModelStatement := by
  intro r ds a B hB
  obtain ⟨N, hN⟩ := hB.2
  let d := 2 * N + 1
  let I := matrixModel ℝ (r + 1)
  let R := HeightWeightedRightTranslation.representation
    (A := Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ) d
  let W (f : Automorphic.realStandardKFinite (r + 1) ds) := hasHeightDerivativeBound_of_uniform hB.1 hN f
  let J₀ : Automorphic.realStandardKFinite (r + 1) ds →ₗ[ℂ] Archimedean.smoothVectors I R := {
    toFun f := ⟨weightedVector (W f), weightedVector_isSmooth (W f)⟩
    map_add' f f' := by
      apply Subtype.ext
      ext g
      change weightedVector (W (f + f')) g = weightedVector (W f) g + weightedVector (W f') g
      simp only [weightedVector_apply, map_add, Pi.add_apply, smul_add]
    map_smul' c f := by
      apply Subtype.ext
      ext g
      change weightedVector (W (c • f)) g = c • weightedVector (W f) g
      simp only [weightedVector_apply, map_smul, Pi.smul_apply]
      exact smul_comm _ _ _ }
  let J := (DerivativeSmoothVectors.toSmooth I R).symm.toLinearMap.comp J₀
  refine ⟨d, J, ⟨?_, ?_⟩, ?_⟩
  · intro k f
    let f' := realStandardRep (r + 1) ds k f
    let k' : unitaryCompact ℝ (r + 1) := ⟨Unitary.toUnits k, k.property⟩
    have hAct : B f' = Whittaker.rightTranslation ℂ (Langlands.GeneralLinear (r + 1) ℝ)
        (Unitary.toUnits k) (B f) :=
      hB.1.2.2.2.1 k' f f' (realStandardRep_apply_coe (r + 1) ds k f)
    apply (DerivativeSmoothVectors.toSmooth I R).injective
    rw [DerivativeSmoothVectors.toSmooth_representation]
    apply Subtype.ext
    ext x
    change weightedVector (W f') x = R (Unitary.toUnits k) (weightedVector (W f)) x
    rw [translate_weightedVector_apply, weightedVector_apply, hAct]
    rfl
  · intro X f
    let f' := realStandardLie (r + 1) ds ((1 : ℂ) ⊗ₜ[ℝ] X) f
    have hAct : B f' = rightDerivative I X (B f) :=
      hB.1.2.2.2.2 X f f' (realStandardLie_one_tmul_apply_coe (r + 1) ds X f)
    apply (DerivativeSmoothVectors.toSmooth I R).injective
    apply Subtype.ext
    change weightedVector (W f') = lieDerivative I R X (weightedVector (W f))
    rw [lieDerivative_weightedVector]
    ext x
    simp only [weightedVector_apply, hAct]
    rfl
  · intro f g
    rw [evaluation_apply, DerivativeSmoothVectors.toSmooth_representation]
    let H := Archimedean.unitHeight (1 : Langlands.GeneralLinear (r + 1) ℝ)
    change H ^ d • R g (weightedVector (W f)) 1 = _
    rw [translate_weightedVector_apply, ← mul_smul, one_mul]
    have hH : H ≠ 0 := (zero_lt_one.trans_le (Archimedean.one_le_unitHeight _)).ne'
    rw [show 2 * N + 1 = d from rfl, mul_inv_cancel₀ (pow_ne_zero _ hH), one_smul]

end Langlands.Global.RankinSelbergGlobal.RealWhittakerBanachModel
