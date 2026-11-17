import Langlands.Global.RankinSelberg.WhittakerSimpleRootMoments
import Langlands.Global.RankinSelberg.WhittakerExpansionCore.WhittakerFrequency

/-! # Rapid decay in the archimedean simple roots -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj Classical
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.Unfolding

open Langlands.Automorphic.CuspidalWhittaker
open Langlands.GroupScheme.GeneralLinear

local instance simpleRootDecaySchemeAffine (F : Type u) [Field F] (n : ℕ) :
    IsAffine (Scheme F n).X.left := GroupScheme.GeneralLinear.isAffine_groupScheme _ _

variable (F : Type u) [Field F] [NumberField F]

/-- Finitely many mixed trace frequencies detect every mixed-space element. -/
theorem exists_norm_le_sum_mixedTrace_mul {b : F} (hb : b ≠ 0) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ z : mixedEmbedding.mixedSpace F,
      ‖z‖ ≤ K * ∑ k, |mixedTrace F
        (mixedEmbedding F b * (z * mixedEmbedding.latticeBasis F k))| := by
  let Λ := (mixedTracePairing F).comp (LinearMap.mulLeft ℝ (mixedEmbedding F b))
  have hinj : Function.Injective Λ := by
    intro z z' h
    have h1 := mixedTracePairing_injective F h
    simp only [LinearMap.mulLeft_apply] at h1
    have hb' : mixedEmbedding F b⁻¹ * mixedEmbedding F b = 1 := by
      rw [← map_mul, inv_mul_cancel₀ hb, map_one]
    calc z = mixedEmbedding F b⁻¹ * (mixedEmbedding F b * z) := by
          rw [← mul_assoc, hb', one_mul]
      _ = mixedEmbedding F b⁻¹ * (mixedEmbedding F b * z') := by rw [h1]
      _ = z' := by rw [← mul_assoc, hb', one_mul]
  obtain ⟨K, hK, hΛ⟩ := EqualAnalytic.exists_norm_le_sum_of_injective Λ hinj
  refine ⟨K, hK, fun z => (hΛ z).trans (le_of_eq ?_)⟩
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  simp only [Λ, LinearMap.comp_apply, LinearMap.mulLeft_apply, mixedTracePairing,
    LinearMap.pi_apply]
  congr 2
  ring

variable {r : ℕ} {V : Submodule ℂ (Points F (r + 1) → ℂ)}
    {R : ArchimedeanMatrix F (r + 1) →ₗ[ℝ] V →ₗ[ℂ] V}

/-- A common determinant exponent gives arbitrary rapid decay in the entire
archimedean simple-root row, uniformly over compact right factors. -/
theorem exists_simpleRoot_row_decay_of_detPower
    [CompactSpace (AdeleQuotient F)]
    (hV : WhittakerDecayClass F r V R) (β : ℝ)
    (hβ : ∀ f : V, ∃ B : ℝ, 0 ≤ B ∧ ∀ g : Points F (r + 1),
      ‖(f : Points F (r + 1) → ℂ) g‖ ≤ B * detNorm F (r + 1) g ^ β)
    (ψ : AddChar (Adeles F) ℂ) (hψ : IsStandardAdditiveCharacter F ψ)
    (N : ℕ) (f : V) {C : Set (Points F (r + 1))} (hC : IsCompact C) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ (a : Points F (r + 1)) (d : Fin (r + 1) → (mixedEmbedding.mixedSpace F)ˣ),
        archCoord F a = diagonalMatrixUnits (mixedEmbedding.mixedSpace F) d →
      ∀ k ∈ C,
        (1 + ‖fun i : Fin r =>
          (d i.castSucc : mixedEmbedding.mixedSpace F) *
            ((d i.succ)⁻¹ : (mixedEmbedding.mixedSpace F)ˣ)‖) ^ N *
          ‖whittaker F r ψ (f : Points F (r + 1) → ℂ) (a * k)‖ ≤
          B * detNorm F (r + 1) (a * k) ^ β := by
  obtain ⟨b, hb0, hb⟩ := EqualAnalytic.exists_eq_standardCharacter_mul F ψ hψ
  obtain ⟨K, hK, hsize⟩ := exists_norm_le_sum_mixedTrace_mul F hb0
  let M : ℝ := ∑ j, ‖mixedEmbedding.latticeBasis F j‖
  have hM : 0 ≤ M := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have he : ∀ j, ‖mixedEmbedding.latticeBasis F j‖ ≤ M := fun j =>
    Finset.single_le_sum (f := fun j => ‖mixedEmbedding.latticeBasis F j‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_univ j)
  obtain ⟨B₁, hB₁, hmom⟩ :=
    exists_simpleRoot_frequency_moment_bound F hV β hβ N f hC M hM
  obtain ⟨B₀, hB₀, hbase⟩ := hβ f
  let Idx := Fin r × Module.Free.ChooseBasisIndex ℤ (𝓞 F)
  let P : ℝ := (1 + K) ^ N * (Fintype.card (Option Idx) : ℝ) ^ N
  have hP : 0 ≤ P := by dsimp [P]; positivity
  refine ⟨P * (B₀ + (Fintype.card Idx : ℝ) * B₁), by positivity, ?_⟩
  intro a d ha k hk
  let z : Fin r → mixedEmbedding.mixedSpace F := fun i =>
    (d i.castSucc : mixedEmbedding.mixedSpace F) *
      ((d i.succ)⁻¹ : (mixedEmbedding.mixedSpace F)ˣ)
  let L : Idx → ℝ := fun p =>
    mixedTrace F (mixedEmbedding F b * (z p.1 * mixedEmbedding.latticeBasis F p.2))
  let W : ℝ := ‖whittaker F r ψ (f : Points F (r + 1) → ℂ) (a * k)‖
  let D : ℝ := detNorm F (r + 1) (a * k) ^ β
  have hW : 0 ≤ W := norm_nonneg _
  have hWbound : W ≤ B₀ * D :=
    norm_whittaker_le_of_detPower F ψ hψ _ β B₀ hbase (a * k)
  have hmom' : ∀ p : Idx, |L p| ^ N * W ≤ B₁ * D :=
    fun p => hmom ψ hψ b hb p.1 a d ha k hk
      (mixedEmbedding.latticeBasis F p.2) (he p.2)
  have hsum : 0 ≤ ∑ p, |L p| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hz : ‖z‖ ≤ K * ∑ p, |L p| := by
    refine (pi_norm_le_iff_of_nonneg (mul_nonneg hK hsum)).mpr fun i => ?_
    refine (hsize (z i)).trans (mul_le_mul_of_nonneg_left ?_ hK)
    calc
      ∑ j, |mixedTrace F
          (mixedEmbedding F b * (z i * mixedEmbedding.latticeBasis F j))| =
          ∑ j, |L (i, j)| := rfl
      _ ≤ ∑ i' : Fin r, ∑ j, |L (i', j)| :=
        Finset.single_le_sum (f := fun i' : Fin r => ∑ j, |L (i', j)|)
          (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ i)
      _ = ∑ p, |L p| := (Fintype.sum_prod_type
        (α₁ := Fin r) (α₂ := Module.Free.ChooseBasisIndex ℤ (𝓞 F))
          fun p => |L p|).symm
  have hsumPow : (1 + ∑ p, |L p|) ^ N ≤
      (Fintype.card (Option Idx) : ℝ) ^ N * (1 + ∑ p, |L p| ^ N) := by
    have h := sum_pow_le_card_pow_mul_sum_pow
      (fun o : Option Idx => o.elim 1 fun p => |L p|)
      (fun o => by cases o <;> simp [abs_nonneg]) N
    simpa only [Fintype.sum_option, Option.elim_none, Option.elim_some, one_pow] using h
  have hrow : (1 + ‖z‖) ^ N ≤ P * (1 + ∑ p, |L p| ^ N) := by
    have h : 1 + ‖z‖ ≤ (1 + K) * (1 + ∑ p, |L p|) := by nlinarith
    calc
      (1 + ‖z‖) ^ N ≤ ((1 + K) * (1 + ∑ p, |L p|)) ^ N :=
        pow_le_pow_left₀ (by positivity) h N
      _ = (1 + K) ^ N * (1 + ∑ p, |L p|) ^ N := mul_pow _ _ _
      _ ≤ _ := by
        dsimp [P]
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left hsumPow (by positivity)
  have hmomSum : (∑ p, |L p| ^ N) * W ≤ (Fintype.card Idx : ℝ) * (B₁ * D) := by
    rw [Finset.sum_mul]
    calc
      ∑ p, |L p| ^ N * W ≤ ∑ _p : Idx, B₁ * D :=
        Finset.sum_le_sum fun p _ => hmom' p
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  calc
    (1 + ‖z‖) ^ N * W ≤ P * (1 + ∑ p, |L p| ^ N) * W :=
      mul_le_mul_of_nonneg_right hrow hW
    _ = P * (W + (∑ p, |L p| ^ N) * W) := by ring
    _ ≤ P * (B₀ * D + (Fintype.card Idx : ℝ) * (B₁ * D)) :=
      mul_le_mul_of_nonneg_left (add_le_add hWbound hmomSum) hP
    _ = P * (B₀ + (Fintype.card Idx : ℝ) * B₁) * D := by ring

end Langlands.Global.RankinSelbergGlobal.Unfolding
