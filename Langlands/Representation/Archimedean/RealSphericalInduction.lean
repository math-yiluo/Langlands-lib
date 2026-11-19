import Langlands.Representation.Archimedean.RealSphericalLimit
import Langlands.Representation.Archimedean.JacquetKernel

/-!
# Submodules of the dual unramified principal series orthogonal to the spherical vector

Let `χ` be signed-power characters on `GL_n(ℝ)` with exponents `e` and trivial signs, whose real
parts weakly decrease. Every subspace `U` of the `O(n)`-finite functions of the principal series
of `χ⁻¹` that is stable under `O(n)` and under right derivatives, and whose functions all have
integral `0` over `O(n)`, is zero. The proof is by induction on `n` along the maximal parabolic
subgroup `P_{n-1,1}`.
-/

noncomputable section

open MeasureTheory Matrix

open scoped Manifold ContDiff Matrix.Norms.Operator

namespace Langlands.Archimedean

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace RealSphericalInduction

open MaximalParabolicIntegration ParabolicChartBound PartialJacquet JacquetLimit JacquetDual
  JacquetNonvanishing GramFormula Langlands.GeneralLinear RealPrincipalSeriesDuality
  RealSphericalChart

attribute [local instance] measurableSpaceK

local instance borelSpaceK_rsi (n : ℕ) : BorelSpace (unitaryCompact ℝ n) := ⟨rfl⟩

variable {e : ℕ → ℂ} {m : ℕ}

theorem dualChar_dualChar (χ : ℕ → ℝˣ → ℂ) : dualChar (dualChar χ) = χ := by
  funext l x
  simp [dualChar]

theorem re_le_of_le (he : IsWeaklyDominant e m) {j k : ℕ} (hjk : j ≤ k)
    (hkm : k ≤ m) : (e k).re ≤ (e j).re := by
  induction k, hjk using Nat.le_induction with
  | base => exact le_rfl
  | succ k hjk ih => exact (he k (by omega)).trans (ih (by omega))

theorem isWeaklyDominant_shift (he : IsWeaklyDominant e m) :
    IsWeaklyDominant (fun l => e l - 1 / 2) (m - 1) := by
  intro l hl
  have := he l (by omega)
  simp only [Complex.sub_re]
  linarith

theorem sub_sub_one_ne_zero (he : IsWeaklyDominant e m) :
    ∀ j : ℕ, j < m → e m - e j - 1 ≠ 0 := by
  intro j hj h
  have h1 := re_le_of_le he hj.le le_rfl
  have h2 := congrArg Complex.re h
  simp only [Complex.sub_re, Complex.one_re, Complex.zero_re] at h2
  linarith

theorem spherical_of_mem {n : ℕ} {k : Langlands.GeneralLinear n ℝ}
    (hk : k ∈ unitaryCompact ℝ n) : signVector n e (fun _ => 0) (fun _ => 0) k = 1 := by
  rw [signVector_of_mem _ _ hk]
  simp [signMonomial]

/-- **Orthogonality to the spherical vector.** -/
theorem eq_bot : ∀ (n : ℕ) {χ : ℕ → ℝˣ → ℂ} {e : ℕ → ℂ}, IsSignedPower χ e →
    (∀ l, χ l (-1) = 1) → IsWeaklyDominant e (n - 1) →
    ∀ {U : Submodule ℂ (Langlands.GeneralLinear n ℝ → ℂ)},
    U ≤ kFiniteFunctions (principalSeries ℝ n (dualChar χ)) (unitaryCompact ℝ n) →
    (∀ k ∈ unitaryCompact ℝ n, ∀ u ∈ U,
      Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℝ) k u ∈ U) →
    (∀ (X : Matrix (Fin n) (Fin n) ℝ), ∀ u ∈ U, rightDerivative (matrixModel ℝ n) X u ∈ U) →
    (∀ u ∈ U, ∫ k, u (k : Langlands.GeneralLinear n ℝ) ∂haarK n = 0) →
    U = ⊥
  | 0, χ, e, _, _, _, U, _, _, _, hint => by
      rw [Submodule.eq_bot_iff]
      intro u hu
      have hsub : ∀ g : Langlands.GeneralLinear 0 ℝ, g = 1 := fun g => Subsingleton.elim _ _
      have h1 := hint u hu
      have hconst : (fun k : unitaryCompact ℝ 0 => u (k : Langlands.GeneralLinear 0 ℝ)) =
          fun _ => u 1 := funext fun k => by rw [hsub k]
      rw [hconst, integral_const, probReal_univ, one_smul] at h1
      exact funext fun g => by rw [hsub g]; exact h1
  | m + 1, χ, e, hχ, hp, he, U, hU, hUK, hUD, hint => by
      have he' : IsWeaklyDominant e m := by simpa using he
      set A := JacquetKernel.annihilator (dualChar χ) U hU with hAdef
      have hA : A ≤ kFiniteFunctions (principalSeries ℝ (m + 1) χ)
          (unitaryCompact ℝ (m + 1)) := by
        have h1 := JacquetKernel.annihilator_le (χ := dualChar χ) U hU
        rwa [dualChar_dualChar] at h1
      have hAD := JacquetKernel.annihilator_rightDerivative hχ.dual U hU hUD
      have hT : signVector (m + 1) e (fun _ => 0) (fun _ => 0) ∈ A := by
        refine ⟨?_, fun u hu => ?_⟩
        · rw [dualChar_dualChar]
          exact signVector_mem _ _ hχ (sign_zero hp)
        · calc ∫ k, signVector (m + 1) e (fun _ => 0) (fun _ => 0)
                (k : Langlands.GeneralLinear (m + 1) ℝ) * u k ∂haarK (m + 1)
              = ∫ k, u (k : Langlands.GeneralLinear (m + 1) ℝ) ∂haarK (m + 1) :=
                integral_congr_ae (ae_of_all _ fun k => by
                  simp only
                  rw [spherical_of_mem k.2, one_mul])
            _ = 0 := hint u hu
      have hH := RealSphericalReach.regularized_mem hχ hp hA hAD (sub_sub_one_ne_zero he') hT
      have hHc : Continuous (signVector (m + 1) e (fun _ => 0) (bump (fun _ => 0) m 1)) :=
        (signVector_mem _ _ hχ (sign_zero hp)).1.1.continuous
      have horth : ∀ u ∈ U, ∫ k, u (k : Langlands.GeneralLinear (m + 1) ℝ) *
          signVector (m + 1) e (fun _ => 0) (bump (fun _ => 0) m 1) k ∂haarK (m + 1) = 0 :=
        fun u hu => (integral_congr_ae (ae_of_all _ fun k => mul_comm _ _)).trans (hH.2 u hu)
      have hF3 := integral_mul_eq_zero_of_orthogonal hχ hU hUK hUD hHc horth
      have hlim : ∀ u ∈ U, ∫ k, u (iotaGL (k : Langlands.GeneralLinear m ℝ)) ∂haarK m = 0 :=
        fun u hu => RealSphericalLimit.integral_iota_eq_zero hχ hp he' (hU hu).1 (hF3 u hu)
      have hUM : U.map restrictLevi ≤
          kFiniteFunctions (principalSeries ℝ m (dualChar (shiftChar χ))) (unitaryCompact ℝ m) := by
        rintro _ ⟨u, hu, rfl⟩
        exact restrictLevi_mem hχ (hU hu)
      have hUMK : ∀ k ∈ unitaryCompact ℝ m, ∀ u ∈ U.map restrictLevi,
          Whittaker.rightTranslation ℂ (Langlands.GeneralLinear m ℝ) k u ∈ U.map restrictLevi := by
        rintro k hk _ ⟨u, hu, rfl⟩
        rw [rightTranslation_restrictLevi]
        exact ⟨_, hUK _ (iotaGL_mem_unitaryCompact hk) u hu, rfl⟩
      have hUMD : ∀ (X : Matrix (Fin m) (Fin m) ℝ), ∀ u ∈ U.map restrictLevi,
          rightDerivative (matrixModel ℝ m) X u ∈ U.map restrictLevi := by
        rintro X _ ⟨u, hu, rfl⟩
        rw [rightDerivative_restrictLevi (hU hu).1.1]
        exact ⟨_, hUD _ u hu, rfl⟩
      have hbot := eq_bot m hχ.shift (fun l => by rw [shiftChar_neg_one, hp])
        (isWeaklyDominant_shift he') hUM hUMK hUMD (by rintro _ ⟨u, hu, rfl⟩; exact hlim u hu)
      by_contra hU0
      exact map_restrictLevi_ne_bot hU hUK hU0 hbot

end RealSphericalInduction

end Langlands.Archimedean
