import Langlands.Representation.Archimedean.ComplexJacquetLimitSum
import Langlands.Representation.Archimedean.ComplexReverseTwist

/-!
# Matrix coefficients related by transposition and the Jacquet integral

If two `U(n)`-integral matrix coefficients `M_{x,y}(g) = ∫_{U(n)} x(κ g) y(κ) dκ` satisfy
`M_{x₁,y₁}(g) = M_{x₂,y₂}(gᵀ)` for all `g ∈ GL_n(ℂ)`, with `xᵢ` in the dual principal series and
`yᵢ` in a strictly dominant principal series, then `x₁(1) Λ_n(y₁) = x₂(1) Λ_n(y₂)` for the Jacquet
integral `Λ_n` in stages.
-/

noncomputable section

open MeasureTheory Matrix Filter Topology

open scoped Manifold ContDiff Matrix.Norms.Operator ComplexConjugate

namespace Langlands.Archimedean

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace ComplexReverseRecursion

open ComplexMaximalParabolicIntegration ComplexParabolicChartBound ComplexPartialJacquet
  ComplexGramFormula Langlands.GeneralLinear ComplexDuality ComplexKIntegralInvariance
  ComplexJacquetLimit ComplexJacquetDual ComplexReverseTwist

variable {m : ℕ} {χ : ℕ → ℂˣ → ℂ} {e : ℕ → ℂ}

/-! ## Transposition of the Levi embedding and of `d(s)` -/

theorem iota_transpose (A : Matrix (Fin m) (Fin m) ℂ) : (iota A)ᵀ = iota Aᵀ := by
  ext i j
  refine Fin.lastCases ?_ (fun i' => ?_) i <;> refine Fin.lastCases ?_ (fun j' => ?_) j <;>
    simp [iota]

theorem transposeGL_iotaGL (g : Langlands.GeneralLinear m ℂ) :
    transposeGL (iotaGL g) = iotaGL (transposeGL g) :=
  Units.ext (by rw [transposeGL_val, iotaGL_val, iotaGL_val, transposeGL_val, iota_transpose])

theorem transposeGL_dlastGL (s : ℂˣ) : transposeGL (dlastGL (m := m) s) = dlastGL s :=
  Units.ext (by rw [transposeGL_val, dlastGL_val, dlast, Matrix.diagonal_transpose])

/-! ## The `GL_n(ℂ)`-invariance of the pairing -/

/-- **Swapping a matrix coefficient.** For `w` in the principal series of `χ` and `u` in that of
`χ⁻¹`, `∫ w(κ g) u(κ) dκ = ∫ u(κ g⁻¹) w(κ) dκ`. -/
theorem integral_mul_swap {n : ℕ} (hχ : IsPhasePower χ e) {w u : Langlands.GeneralLinear n ℂ → ℂ}
    (hw : w ∈ principalSeries ℂ n χ) (hu : u ∈ principalSeries ℂ n (dualChar χ))
    (g : Langlands.GeneralLinear n ℂ) :
    ∫ κ, w ((κ : Langlands.GeneralLinear n ℂ) * g) * u κ ∂unitaryHaar n =
      ∫ κ, u ((κ : Langlands.GeneralLinear n ℂ) * g⁻¹) * w κ ∂unitaryHaar n := by
  have hud := rightTranslation_mem_principalSeries (χ := dualChar χ) hu g⁻¹
  set F : Langlands.GeneralLinear n ℂ → ℂ := fun y => u (y * g⁻¹) * w y with hFdef
  have hF : F ∈ principalSeries ℂ n (modulusCharacter n) := by
    refine ⟨contMDiff_mul_fun hud.1 hw.1, fun a v y => ?_⟩
    simp only [hFdef]
    rw [mul_assoc _ y, hu.2 a v, hw.2 a v y, ← principalSeriesCharacter_dual_mul hχ]
    ring
  have h1 := integral_mul_eq hF g
  simp only [hFdef, mul_assoc, mul_inv_cancel, mul_one] at h1
  rw [← h1]
  exact integral_congr_ae (ae_of_all _ fun κ => mul_comm _ _)

/-! ## The recursion -/

/-- **Transposed matrix coefficients and the Jacquet integral.** Let `χ` be strictly dominant
phase-power characters, `x₁, x₂` `U(n)`-finite functions of the principal series of `χ⁻¹` and
`y₁, y₂` `U(n)`-finite functions of the principal series of `χ`. If
`∫ x₁(κ g) y₁(κ) dκ = ∫ x₂(κ gᵀ) y₂(κ) dκ` for every `g ∈ GL_n(ℂ)`, then
`x₁(1) Λ_n(y₁) = x₂(1) Λ_n(y₂)`. -/
theorem mul_jacquet_eq_of_transpose : ∀ (n : ℕ) {χ : ℕ → ℂˣ → ℂ} {e : ℕ → ℂ},
    IsPhasePower χ e → IsStrictlyDominant e (n - 1) →
    ∀ {x₁ y₁ x₂ y₂ : Langlands.GeneralLinear n ℂ → ℂ},
    x₁ ∈ kFiniteFunctions (principalSeries ℂ n (dualChar χ)) (unitaryCompact ℂ n) →
    y₁ ∈ kFiniteFunctions (principalSeries ℂ n χ) (unitaryCompact ℂ n) →
    x₂ ∈ kFiniteFunctions (principalSeries ℂ n (dualChar χ)) (unitaryCompact ℂ n) →
    y₂ ∈ kFiniteFunctions (principalSeries ℂ n χ) (unitaryCompact ℂ n) →
    (∀ g : Langlands.GeneralLinear n ℂ,
      ∫ κ, x₁ ((κ : Langlands.GeneralLinear n ℂ) * g) * y₁ κ ∂unitaryHaar n =
        ∫ κ, x₂ ((κ : Langlands.GeneralLinear n ℂ) * transposeGL g) * y₂ κ ∂unitaryHaar n) →
    x₁ 1 * jacquet n y₁ = x₂ 1 * jacquet n y₂
  | 0, χ, e, _, _, x₁, y₁, x₂, y₂, _, _, _, _, hM => by
      have hsub : ∀ g : Langlands.GeneralLinear 0 ℂ, g = 1 := fun g => Subsingleton.elim _ _
      have h1 := hM 1
      have hc : ∀ (x y : Langlands.GeneralLinear 0 ℂ → ℂ) (g : Langlands.GeneralLinear 0 ℂ),
          (fun κ : unitaryCompact ℂ 0 => x ((κ : Langlands.GeneralLinear 0 ℂ) * g) * y κ) =
            fun _ => x 1 * y 1 := fun x y g => funext fun κ => by
        rw [hsub ((κ : Langlands.GeneralLinear 0 ℂ) * g), hsub (κ : Langlands.GeneralLinear 0 ℂ)]
      rw [hc x₁ y₁ 1, hc x₂ y₂ (transposeGL 1), integral_const, integral_const, probReal_univ,
        one_smul, one_smul] at h1
      exact h1
  | m + 1, χ, e, hχ, he, x₁, y₁, x₂, y₂, hx₁, hy₁, hx₂, hy₂, hM => by
      have he' : IsStrictlyDominant e m := by simpa using he
      -- the identity on `GL_m(ℂ)` after the limit along the ray `d(s)`
      have hstep : ∀ g : Langlands.GeneralLinear m ℂ,
          ∫ k, restrictLevi x₁ ((k : Langlands.GeneralLinear m ℂ) * g) * jacquetStep y₁ k
            ∂unitaryHaar m =
          ∫ k, restrictLevi x₂ ((k : Langlands.GeneralLinear m ℂ) * transposeGL g) *
            jacquetStep y₂ k ∂unitaryHaar m := by
        intro g
        have hr := ComplexJacquetLimitSum.integral_mul_jacquetStep_eq_of_ray hχ he'
          (u₁ := Whittaker.rightTranslation ℂ (Langlands.GeneralLinear (m + 1) ℂ) (iotaGL g) x₁)
          (h₁ := y₁)
          (u₂ := Whittaker.rightTranslation ℂ (Langlands.GeneralLinear (m + 1) ℂ)
            (iotaGL (transposeGL g)) x₂) (h₂ := y₂)
          (rightTranslation_mem_principalSeries (χ := dualChar χ) hx₁.1 (iotaGL g)) hy₁.1
          (rightTranslation_mem_principalSeries (χ := dualChar χ) hx₂.1
            (iotaGL (transposeGL g))) hy₂.1 (fun s => by
            have h := hM (dlastGL s * iotaGL g)
            rw [transposeGL_mul, transposeGL_iotaGL, transposeGL_dlastGL,
              iotaGL_mul_dlastGL] at h
            show ∫ κ, x₁ ((κ : Langlands.GeneralLinear (m + 1) ℂ) * dlastGL s * iotaGL g) *
                y₁ κ ∂unitaryHaar (m + 1) =
              ∫ κ, x₂ ((κ : Langlands.GeneralLinear (m + 1) ℂ) * dlastGL s *
                iotaGL (transposeGL g)) * y₂ κ ∂unitaryHaar (m + 1)
            simp only [mul_assoc]
            exact h)
        simp only [restrictLevi_apply, map_mul]
        exact hr
      have ih := mul_jacquet_eq_of_transpose m hχ.shift (isStrictlyDominant_shift he')
        (restrictLevi_mem hχ hx₁) (jacquetStep_mem hχ he' hy₁) (restrictLevi_mem hχ hx₂)
        (jacquetStep_mem hχ he' hy₂) hstep
      simp only [restrictLevi_apply, map_one] at ih
      exact ih

end ComplexReverseRecursion

end Langlands.Archimedean
