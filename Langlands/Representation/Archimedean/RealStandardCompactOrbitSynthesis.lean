import Langlands.Global.RankinSelberg.RealStandardCompactFinite
import Langlands.Representation.Archimedean.BanachModerateGrowth
import Langlands.Representation.Archimedean.OrthogonalConvolutionDegree
import Langlands.Representation.Archimedean.RealSmoothCompactWeightedTransfer
import Langlands.Representation.Archimedean.RealStandardModuleAdmissible
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! # Compact convolution of translates of real standard vectors -/

noncomputable section

open MeasureTheory Set
open scoped Matrix Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean

open DerivativeSmoothVectors OrthogonalFinitePolynomial
open Langlands.Global.RankinSelbergGlobal.RealStandardCompactBanach
open Langlands.LocalFactor.Archimedean

universe uE

variable {n : ℕ}

local notation "G" n:max => Langlands.GeneralLinear n ℝ
local notation "O" n:max => Matrix.unitaryGroup (Fin n) ℝ
local notation "M" n:max => Matrix (Fin n) (Fin n) ℝ
local notation "V" n:max ds:max => kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n)
local notation "D" n:max R:max => DerivativeSmoothVectors (matrixModel ℝ n) R
local notation:max "ε" n:max R:max => derivativeCLM (matrixModel ℝ n) R []
local notation:max "R₀" n:max ds:max =>
  Langlands.Global.RankinSelbergGlobal.RealStandardCompactBanach.representation (n := n) ds

/-- The continuous compact profile of a compact-finite real standard vector. -/
def compactFiniteProfile (ds : List RealBlock) : (V n ds) →ₗ[ℂ] C(O n, ℂ) :=
  (compactRestriction ds).comp (Submodule.inclusion inf_le_left)

@[simp]
theorem compactFiniteProfile_apply (ds : List RealBlock) (v : V n ds) (k : O n) :
    compactFiniteProfile ds v k = v.val (Unitary.toUnits k) := rfl

theorem injective_compactFiniteProfile (ds : List RealBlock) :
    Function.Injective (compactFiniteProfile (n := n) ds) := by
  intro u v h
  have he : embed ds ⟨u.val, u.property.1⟩ = embed ds ⟨v.val, v.property.1⟩ := Subtype.ext h
  exact Subtype.ext (congrArg (fun f : realStandardModule n ds => f.val) (embed_injective ds he))

/-- The compact profile of a scaled full-group translate of a compact-finite seed. -/
def translatedSeedProfile (ds : List RealBlock) (b : ℂ) (g : G n) (v : V n ds) : C(O n, ℂ) :=
  (b • R₀ n ds g (embed ds ⟨v.val, v.property.1⟩)).val

@[simp]
theorem translatedSeedProfile_apply (ds : List RealBlock) (b : ℂ) (g : G n)
    (v : V n ds) (k : O n) :
    translatedSeedProfile ds b g v k = b * v.val (Unitary.toUnits k * g) := by
  simp only [translatedSeedProfile, Submodule.coe_smul, ContinuousMap.smul_apply,
    smul_eq_mul, representation_embed, embed_val, compactRestriction_apply, translate_apply]

private def inverseCompactProfile (ds : List RealBlock) : (V n ds) →ₗ[ℂ] C(O n, ℂ) :=
  (ContinuousMap.compCLM ℂ ℂ (⟨Inv.inv, continuous_inv⟩ : C(O n, O n))).toLinearMap.comp
    (compactFiniteProfile ds)

private theorem inverseCompactProfile_equivariant (ds : List RealBlock)
    (k x : O n) (v : V n ds) :
    inverseCompactProfile ds (realStandardRep n ds k v) x =
      inverseCompactProfile ds v (k⁻¹ * x) := by
  change (realStandardRep n ds k v).val (Unitary.toUnits x⁻¹) =
    v.val (Unitary.toUnits ((k⁻¹ * x)⁻¹))
  rw [realStandardRep_apply_coe, mul_inv_rev, inv_inv, map_mul]
  rfl

/-- Convolving a translated seed profile against a compact-finite profile yields
the profile of a compact-finite vector. The value of every compact and Lie equivariant
map from the standard module is controlled by the seed value and polynomial group height. -/
def RealStandardCompactOrbitSynthesisStatement : Prop :=
  ∀ (n : ℕ) (ds : List RealBlock)
    [MeasurableSpace (O n)] [BorelSpace (O n)] [MeasurableMul (O n)]
    (μ : Measure (O n)) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant] [μ.IsInvInvariant]
    (E : Type uE) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (R : G n →* (E →L[ℂ] E)) (f : (V n ds) →ₗ[ℂ] D n R),
    IsContinuousRepresentation R →
    IsSmoothGKIntertwiner ℝ n R (realStandardRep n ds) (realStandardLie n ds) f →
    ∃ (C : ℝ) (d : ℕ), 0 ≤ C ∧
      ∀ (b : ℂ) (g : G n) (v w : V n ds), ∃ z : V n ds,
        compactFiniteProfile ds z =
          leftConvolution μ (translatedSeedProfile ds b g v) (compactFiniteProfile ds w) ∧
        ‖ε n R (f z)‖ ≤
          C * unitHeight g ^ d * (‖b‖ * ‖ε n R (f v)‖) * ‖compactFiniteProfile ds w‖

set_option maxHeartbeats 800000 in
theorem realStandardCompactOrbitSynthesis : RealStandardCompactOrbitSynthesisStatement.{uE} := by
  intro n ds _ _ _ μ _ _ _ E _ _ _ R f hR hf
  classical
  let ρ := realStandardRep n ds
  let π := realStandardLie n ds
  let e := (smoothKFinite ℝ n (R₀ n ds)).subtype.comp (compactFiniteEquiv ds).toLinearMap
  have hGK : IsRealGKModule n ρ π := isRealGKModule_realStandardModule n ds
  have hadm : IsAdmissibleGKModule ρ := realStandardAdmissible n ds
  have hR₀ : IsContinuousRepresentation (R₀ n ds) :=
    Langlands.Global.RankinSelbergGlobal.RealStandardCompactBanach.isContinuousRepresentation ds
  have he : IsSmoothGKIntertwiner ℝ n (R₀ n ds) ρ π e :=
    isSmoothGKIntertwiner_compactFiniteEquiv ds
  have heinj : Function.Injective e := Subtype.val_injective.comp (compactFiniteEquiv ds).injective
  obtain ⟨C, d, hC, hCd⟩ := exists_norm_le_unitHeight_pow ℝ n R hR
  have hHeight : Continuous (fun x : O n => unitHeight (A := M n) (Unitary.toUnits x)) :=
    continuous_unitHeight.comp (continuous_unitary_toUnits (N := n))
  obtain ⟨B₀, hB₀⟩ := isCompact_univ.exists_bound_of_continuousOn hHeight.continuousOn
  let B := max 1 B₀
  have hB : 0 ≤ B := zero_le_one.trans (le_max_left _ _)
  have hK (k : O n) : unitHeight (A := M n) (Unitary.toUnits k) ≤ B := by
    have hk : |unitHeight (A := M n) (Unitary.toUnits k)| ≤ B₀ := by
      simpa only [Real.norm_eq_abs] using hB₀ k (mem_univ k)
    exact (le_abs_self _).trans (hk.trans (le_max_right _ _))
  let A := C * B ^ d
  have hA : 0 ≤ A := by dsimp [A]; positivity
  refine ⟨A, d, hA, fun b g v w => ?_⟩
  let S := FiniteVectors.orbitSubrepresentation ρ w
  let : FiniteDimensional ℂ S.toSubmodule := hGK.1 w
  let : Module.Free ℂ S.toSubmodule := Module.Free.of_divisionRing ℂ S.toSubmodule
  let basis : Module.Basis (Fin (Module.finrank ℂ S.toSubmodule)) ℂ S.toSubmodule :=
    Module.finBasis ℂ S.toSubmodule
  let τ := KFiniteDual.subMatrix S
  let wS : S.toSubmodule := ⟨w, FiniteVectors.self_mem_orbitSpan ρ w⟩
  let a := basis.equivFun wS
  let F := (inverseCompactProfile ds).comp (S.toSubmodule.subtype.comp basis.equivFun.symm.toLinearMap)
  have hF (k x : O n) (y : Fin (Module.finrank ℂ S.toSubmodule) → ℂ) :
      F (τ k *ᵥ y) x = F y (k⁻¹ * x) := by
    change inverseCompactProfile ds (S.toSubmodule.subtype (basis.equivFun.symm (τ k *ᵥ y))) x =
      inverseCompactProfile ds (S.toSubmodule.subtype (basis.equivFun.symm y)) (k⁻¹ * x)
    rw [← KFiniteDual.coordRep_apply, KFiniteDual.equivFun_symm_coordRep]
    exact inverseCompactProfile_equivariant ds k x (basis.equivFun.symm y : S.toSubmodule)
  have hFa (k : O n) : F a k = compactFiniteProfile ds w k⁻¹ := by
    change inverseCompactProfile ds (S.toSubmodule.subtype (basis.equivFun.symm (basis.equivFun wS))) k = _
    rw [LinearEquiv.symm_apply_apply]
    rfl
  obtain ⟨z, hz₁, hz₂⟩ := realSmoothCompactWeightedTransfer_orthogonal ρ π _ e R f μ
    hGK hadm heinj hR₀ hR he hf τ F hF a g (b • v)
  refine ⟨z, ?_, ?_⟩
  · apply ContinuousMap.ext
    intro x
    let ev := profileEval ds x
    let y := ε n (R₀ n ds) (e (b • v))
    let j : C(O n, G n) := ⟨fun k => Unitary.toUnits k * g,
      (continuous_unitary_toUnits (F := ℝ) (N := n)).mul continuous_const⟩
    let h (k : O n) := F a k • R₀ n ds (j k) y
    have hi : Integrable h μ := integrable_compactWeightedOrbit μ (R₀ n ds) hR₀ j (F a) y
    have hZ := congrArg ev hz₁
    change compactFiniteProfile ds z x = ev (∫ k, h k ∂μ) at hZ
    rw [← ev.integral_comp_comm hi] at hZ
    rw [hZ, leftConvolution_apply_kernel, ← integral_inv_eq_self
      (fun k => compactFiniteProfile ds w k * translatedSeedProfile ds b g v (x * k⁻¹)) μ]
    refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
    change ev (F a k • R₀ n ds (Unitary.toUnits k * g) (embed ds ⟨(b • v).val, (b • v).property.1⟩)) =
      compactFiniteProfile ds w k⁻¹ * translatedSeedProfile ds b g v (x * (k⁻¹)⁻¹)
    rw [map_smul, hFa, smul_eq_mul, inv_inv, translatedSeedProfile_apply]
    congr 1
    let v₀ : realStandardModule n ds := ⟨v.val, v.property.1⟩
    have hscale : (⟨(b • v).val, (b • v).property.1⟩ : realStandardModule n ds) = b • v₀ := rfl
    rw [hscale, map_smul (embed ds), map_smul (R₀ n ds (Unitary.toUnits k * g)),
      map_smul ev, smul_eq_mul, representation_embed]
    change b * v.val (Unitary.toUnits x * (Unitary.toUnits k * g)) =
      b * v.val (Unitary.toUnits (x * k) * g)
    rw [Unitary.toUnits.map_mul, mul_assoc]
  · rw [hz₂]
    have hInt := norm_integral_le_of_norm_le_const (μ := μ) (C :=
      A * unitHeight g ^ d * (‖b‖ * ‖ε n R (f v)‖) * ‖compactFiniteProfile ds w‖)
      (f := fun k : O n => F a k • R (Unitary.toUnits k * g) (ε n R (f (b • v))))
      (Filter.Eventually.of_forall fun k => by
        have hk : ‖R (Unitary.toUnits k * g)‖ ≤ A * unitHeight g ^ d := calc
          _ ≤ C * unitHeight (Unitary.toUnits k * g) ^ d := hCd _
          _ ≤ C * (B * unitHeight g) ^ d := by
            refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by
              exact zero_le_one.trans (one_le_unitHeight _)) ?_ _) hC
            exact (unitHeight_mul_le _ _).trans
              (mul_le_mul_of_nonneg_right (hK k) (zero_le_one.trans (one_le_unitHeight g)))
          _ = _ := by rw [mul_pow]; unfold A; ring
        rw [norm_smul, map_smul f, map_smul (ε n R), map_smul (R (Unitary.toUnits k * g)), norm_smul]
        have hY : ‖R (Unitary.toUnits k * g) (ε n R (f v))‖ ≤
            (A * unitHeight g ^ d) * ‖ε n R (f v)‖ :=
          ((R _).le_opNorm _).trans (mul_le_mul_of_nonneg_right hk (norm_nonneg _))
        have hFnorm : ‖F a k‖ ≤ ‖compactFiniteProfile ds w‖ := by
          rw [hFa]
          exact (compactFiniteProfile ds w).norm_coe_le_norm _
        calc
          _ ≤ ‖compactFiniteProfile ds w‖ * (‖b‖ * ((A * unitHeight g ^ d) * ‖ε n R (f v)‖)) := by
            gcongr
          _ = _ := by ring)
    simpa only [probReal_univ, mul_one] using hInt

end Langlands.Archimedean
