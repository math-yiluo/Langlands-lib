import Langlands.Global.RankinSelberg.ComplexSquareFourierUnitaryAverage

/-! # Fourier transport of finite compact orbit spans -/

noncomputable section

open MeasureTheory
open scoped FourierTransform Matrix.Norms.Operator SchwartzMap
open scoped Langlands.Archimedean.ComplexDuality

namespace Langlands.Global.RankinSelbergGlobal.ComplexAdjacentUnfolding

open Langlands.Archimedean Langlands.Archimedean.ComplexReverseTwist
open Langlands.GeneralLinear
open ComplexSquareFourier (matrixTransform complexSquareFourierUnitaryAverage)

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

variable {r : ℕ}

local notation "G" => Langlands.GeneralLinear (r + 1) ℂ
local notation "K" => unitaryCompact ℂ (r + 1)
local notation "Mat" => Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ

private def leftUnitaryTest (Φ : 𝓢(Mat, ℂ)) (k : K) : 𝓢(Mat, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (Units.mulLeftLinearEquiv ℝ Mat k.val⁻¹).toContinuousLinearEquiv Φ

private theorem matrixTransform_leftUnitary (a : ℂˣ) (Φ : 𝓢(Mat, ℂ)) (k : K) (X : Mat) :
    matrixTransform a (leftUnitaryTest Φ k) X =
      matrixTransform a Φ ((conjK (r + 1) k).val⁻¹.val * X) := by
  let κ := Measure.dirac (1 : K)
  have hmean (Y : Mat) : leftUnitaryTest Φ k Y =
      ∫ _ : K, (1 : ℂ) * Φ ((k⁻¹ : K).val.val * Y * (1 : K).val.val) ∂κ := by
    simpa only [κ, integral_dirac, one_mul, Subgroup.coe_inv, Subgroup.coe_one, Units.val_one,
      Matrix.mul_one]
      using (show leftUnitaryTest Φ k Y = Φ (k.val⁻¹.val * Y) from rfl)
  have h := complexSquareFourierUnitaryAverage κ a (fun _ => (1 : ℂ))
    (fun _ => k⁻¹) (fun _ => (1 : K)) continuous_const continuous_const continuous_const
    Φ (leftUnitaryTest Φ k) hmean X
  simpa only [κ, integral_dirac, one_mul, map_inv, map_one, Subgroup.coe_inv, Subgroup.coe_one,
    Units.val_one, Matrix.mul_one] using h

private def matrixTransformLinear (a : ℂˣ) : 𝓢(Mat, ℂ) →ₗ[ℂ] 𝓢(Mat, ℂ) where
  toFun := matrixTransform a
  map_add' Φ Ψ := by
    simp only [matrixTransform, ComplexTraceFourier.transform, ← SchwartzMap.fourierTransformCLM_apply ℂ,
      map_add, smul_add]
  map_smul' c Φ := by
    simp only [matrixTransform, ComplexTraceFourier.transform, ← SchwartzMap.fourierTransformCLM_apply ℂ,
      map_smul, RingHom.id_apply]
    rw [smul_comm]
    simp only [map_smul]

/-- The square Fourier transform preserves finite left unitary orbit span. -/
def ComplexAdjacentCompactTransportStatement : Prop :=
  ∀ (a : ℂˣ) (Φ : 𝓢(Mat, ℂ)),
    FiniteDimensional ℂ
      (Submodule.span ℂ (Set.range fun k : K => fun X => Φ (k.val⁻¹.val * X))) →
    FiniteDimensional ℂ (Submodule.span ℂ
      (Set.range fun k : K => fun X => matrixTransform a Φ (k.val⁻¹.val * X)))

theorem complexAdjacentCompactTransport : ComplexAdjacentCompactTransportStatement (r := r) := by
  intro a Φ hΦ
  let S := Submodule.span ℂ (Set.range (leftUnitaryTest Φ))
  let ev : 𝓢(Mat, ℂ) →ₗ[ℂ] (Mat → ℂ) :=
    { toFun := fun Ψ => Ψ
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let T := Submodule.span ℂ (Set.range fun k : K => fun X => Φ (k.val⁻¹.val * X))
  have hST : S.map ev = T := by
    dsimp only [S]
    rw [Submodule.map_span, ← Set.range_comp]
    rfl
  let : FiniteDimensional ℂ T := hΦ
  let i : S →ₗ[ℂ] T := (ev.comp S.subtype).codRestrict T fun f =>
    hST ▸ Submodule.mem_map_of_mem f.2
  let : FiniteDimensional ℂ S := FiniteDimensional.of_injective i fun f g h =>
    Subtype.ext (SchwartzMap.ext fun X => congrFun (congrArg Subtype.val h) X)
  let L := ev.comp (matrixTransformLinear (r := r) a)
  apply Submodule.finiteDimensional_of_le (S₂ := S.map L)
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨k, rfl⟩
  refine ⟨leftUnitaryTest Φ (conjK (r + 1) k), Submodule.subset_span ⟨_, rfl⟩, funext fun X => ?_⟩
  have hc : conjK (r + 1) (conjK (r + 1) k) = k :=
    Subtype.ext (conjAut_conjAut k.val)
  change matrixTransform a (leftUnitaryTest Φ (conjK (r + 1) k)) X = _
  rw [matrixTransform_leftUnitary, hc]

private theorem transferCompactMeasure {K₀ : Type*} [Group K₀] [TopologicalSpace K₀]
    {b₁ b₂ : MeasurableSpace K₀} (h : b₁ = b₂) (κ : @Measure K₀ b₁)
    (hf : letI := b₁; IsFiniteMeasure κ) (hH : letI := b₁; κ.IsHaarMeasure) :
    ∃ κ' : @Measure K₀ b₂, (letI := b₂; IsFiniteMeasure κ') ∧
      (letI := b₂; κ'.IsHaarMeasure) ∧
      ∀ f : K₀ → ℂ, (letI := b₁; ∫ x, f x ∂κ) = (letI := b₂; ∫ x, f x ∂κ') := by
  cases h
  exact ⟨κ, hf, hH, fun _ => rfl⟩

/-- The compact Haar measure can be used with either presentation of its Borel structure. -/
theorem exists_inducedUnitaryMeasure (κ : Measure K) [IsFiniteMeasure κ] [κ.IsHaarMeasure] :
    ∃ κ' : @Measure K ((borel G).comap (Subtype.val : K → G)),
      (letI : MeasurableSpace K := (borel G).comap (Subtype.val : K → G); IsFiniteMeasure κ') ∧
      (letI : MeasurableSpace K := (borel G).comap (Subtype.val : K → G); κ'.IsHaarMeasure) ∧
      ∀ f : K → ℂ, (∫ k, f k ∂κ) =
        (letI : MeasurableSpace K := (borel G).comap (Subtype.val : K → G); ∫ k, f k ∂κ') :=
  transferCompactMeasure (borel_comap (f := (Subtype.val : K → G))) κ ‹_› ‹_›

end Langlands.Global.RankinSelbergGlobal.ComplexAdjacentUnfolding
