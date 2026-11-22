import Langlands.Global.RankinSelberg.RealPrincipalSeriesOrbitWord
import Langlands.Global.RankinSelberg.RealMatrixConvergence
import Langlands.Global.RankinSelberg.RealAdjacentGodementHalfPlane
import Langlands.Global.RankinSelberg.RealLocalEqualFiniteSquareNormalized

/-! # Continuity and half-plane integrability of real principal-series matrix coefficients -/

noncomputable section

open MeasureTheory Set Filter Topology
open Langlands.Archimedean Langlands.LocalFactor.Archimedean
open scoped NNReal SchwartzMap Matrix.Norms.Operator Manifold ContDiff

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal

namespace RealPrincipalSeries

open RealPlaceRestriction

variable (r : ℕ) (ds : List RealBlock)

local notation "G" => Langlands.GeneralLinear (r + 1) ℝ
local notation "Mat" => Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ
local notation "P" => principalSeries ℝ (r + 1) (realPositionCharacter ds)

private def derivativeOp (X : Mat) : P →ₗ[ℂ] P :=
  (rightDerivativeLinearMap P (fun _ h => h.1) X).codRestrict P
    (fun f => rightDerivative_mem_principalSeries _ f.2 X)

private def wordOp (Xs : List Mat) : P →ₗ[ℂ] P :=
  Xs.foldr (fun X B => (derivativeOp r ds X).comp B) LinearMap.id

private theorem wordOp_apply (Xs : List Mat) (f : P) :
    (wordOp r ds Xs f : G → ℂ) = RealLocalWhittaker.iteratedRightDerivative r Xs f := by
  induction Xs with
  | nil => rfl
  | cons X Xs ih =>
    change rightDerivative (matrixModel ℝ (r + 1)) X (wordOp r ds Xs f) =
      rightDerivative (matrixModel ℝ (r + 1)) X (RealLocalWhittaker.iteratedRightDerivative r Xs f)
    rw [ih]

/-- A linear form with a finite compact derivative bound has continuous coefficients
`g ↦ ℓ(π(g) f)`. -/
theorem continuous_translate_coefficient (ℓ : P →ₗ[ℂ] ℂ) (hℓ : HasCompactDerivativeBound r ds ℓ)
    (f : P) : Continuous (fun g : G => ℓ (translate r ds g f)) := by
  obtain ⟨m, Xs, A, hA, hB⟩ := hℓ
  have hK : IsCompact (unitaryCompact ℝ (r + 1) : Set G) := by
    have := isCompact_range (continuous_subtype_val :
      Continuous fun k : unitaryCompact ℝ (r + 1) => (k : G))
    simpa using this
  rw [continuous_iff_continuousAt]
  intro g₀
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨δ, hδ, hδε⟩ : ∃ δ : ℝ, 0 < δ ∧ A * (m * δ) < ε := by
    refine ⟨ε / (A * m + 1), by positivity, ?_⟩
    have hAm : 0 ≤ A * m := mul_nonneg hA (Nat.cast_nonneg m)
    rw [← mul_assoc, mul_div_assoc', div_lt_iff₀ (by positivity)]
    nlinarith
  have hev : ∀ i : Fin m, ∀ᶠ g in 𝓝 g₀, ∀ k ∈ (unitaryCompact ℝ (r + 1) : Set G),
      ‖orbitWord r ds (Xs i) f g k - orbitWord r ds (Xs i) f g₀ k‖ < δ := by
    intro i
    apply hK.eventually_forall_of_forall_eventually
    intro k _
    have hc := continuous_orbitWord r ds (Xs i) f
    have h1 : Tendsto (fun z : G × G => orbitWord r ds (Xs i) f z.1 z.2) (𝓝 (g₀, k))
        (𝓝 (orbitWord r ds (Xs i) f g₀ k)) := hc.continuousAt
    have h2 : Tendsto (fun z : G × G => orbitWord r ds (Xs i) f g₀ z.2) (𝓝 (g₀, k))
        (𝓝 (orbitWord r ds (Xs i) f g₀ k)) :=
      (hc.comp (continuous_const.prodMk continuous_snd)).continuousAt
    have h3 := h1.sub h2
    rw [sub_self] at h3
    filter_upwards [(Metric.tendsto_nhds.mp h3) δ hδ] with z hz
    simpa [dist_eq_norm] using hz
  have hall : ∀ᶠ g in 𝓝 g₀, ∀ i : Fin m, ∀ k ∈ (unitaryCompact ℝ (r + 1) : Set G),
      ‖orbitWord r ds (Xs i) f g k - orbitWord r ds (Xs i) f g₀ k‖ < δ :=
    Filter.eventually_all.mpr hev
  filter_upwards [hall] with g hg
  rw [dist_eq_norm, ← map_sub]
  calc ‖ℓ (translate r ds g f - translate r ds g₀ f)‖ ≤ A * ∑ _i : Fin m, δ := by
        apply hB _ (fun _ => δ)
        intro i k hk
        rw [← wordOp_apply, map_sub, Submodule.coe_sub, Pi.sub_apply, wordOp_apply,
          wordOp_apply]
        exact (hg i k hk).le
    _ = A * (m * δ) := by simp
    _ < ε := hδε

end RealPrincipalSeries

namespace RealGodement

open ArchimedeanLocal Langlands.GeneralLinear
open Langlands.Archimedean.RealJacquetFrobenius (charData charData_character_apply)

private local instance (n : ℕ) : MeasurableSpace (Langlands.GeneralLinear (n + 1) ℝ) := borel _
private local instance (n : ℕ) : BorelSpace (Langlands.GeneralLinear (n + 1) ℝ) := ⟨rfl⟩

variable {t : ℕ}

local notation "m" => (t + 1)
local notation "H" => Langlands.GeneralLinear (t + 2) ℝ
local notation "Y" => Matrix (Fin (t + 2)) (Fin (t + 2)) ℝ
local notation "ιT" => GeneralLinear.inverseTranspose (t + 2) ℝ

/-- The sign character `charData e 0` has modulus one. -/
theorem norm_charData_zero_character (e : Fin 2) (x : ℝˣ) :
    ‖((charData e 0).character x : ℂ)‖ = 1 := by
  rw [charData_character_apply]
  unfold Langlands.Archimedean.RealJacquetFrobenius.charFun
  have hx : (x : ℝ) ≠ 0 := x.ne_zero
  have h1 : abs ((x : ℝ) / |(x : ℝ)|) = 1 := by
    rw [abs_div, abs_abs, div_self (abs_ne_zero.mpr hx)]
  rw [Complex.cpow_zero, mul_one, norm_pow, Complex.norm_real, Real.norm_eq_abs, h1, one_pow]

/-- The weighted matrix integrand equals the matrix zeta kernel of `realMatrixInitialConvergence`
for the coefficient `g ↦ sgn(det g)^e b(g)`. -/
private theorem weightedMatrixTest_mul_eq (e : Fin 2) (Ψ : 𝓢(Y, ℂ)) (b : H → ℂ) (s : ℂ) (g : H) :
    realWeightedMatrixTest (charData e 0) Ψ s g * b g =
      Ψ g.val * (((charData e 0).character (determinant g) : ℂ) * b g) *
        ArchimedeanLocal.detPower (K := ℝ) ArchimedeanLocal.realNormalizedAbs g s := by
  have hpos : (0 : ℝ) < |g.val.det| := abs_pos.mpr (determinant g).ne_zero
  have hpow : ArchimedeanLocal.detPower (K := ℝ) ArchimedeanLocal.realNormalizedAbs g s = ((|g.val.det| : ℝ) : ℂ) ^ s := by
    unfold ArchimedeanLocal.detPower ArchimedeanLocal.realNormalizedAbs
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hpos.ne'),
      ← Complex.ofReal_log hpos.le, mul_comm]
  rw [hpow]
  change Ψ g.val * ((((charData e 0).character (determinant g)) : ℂ) *
      ((|g.val.det| : ℝ) : ℂ) ^ s) * b g = _
  ring

/-- For a matrix coefficient of a linear form with a compact derivative bound, the weighted
matrix integrands of two square Schwartz tests, one with the coefficient and one with the
coefficient composed with the inverse transpose, are integrable for every Haar measure on a
common right half-plane. -/
theorem exists_realWeightedMatrix_integrable (μ : Measure H) [μ.IsHaarMeasure] (e : Fin 2)
    (es : List RealBlock)
    (ℓ : principalSeries ℝ (t + 2) (realPositionCharacter (RealPrincipalSeries.expand es)) →ₗ[ℂ] ℂ)
    (hℓ : RealPrincipalSeries.HasCompactDerivativeBound (t + 1) (RealPrincipalSeries.expand es) ℓ)
    (f : Automorphic.realStandardKFinite (t + 2) es) (Ψ Ψ' : 𝓢(Y, ℂ)) :
    ∃ β : ℝ, ∀ w : ℂ, β < w.re →
      Integrable (fun g => realWeightedMatrixTest (charData e 0) Ψ (w + (m : ℂ) / 2) g *
        realStandardMatrixCoefficient es ℓ f g) μ ∧
      Integrable (fun g => realWeightedMatrixTest (charData e 0) Ψ' (w + (m : ℂ) / 2) g *
        realStandardMatrixCoefficient es ℓ f (ιT g)) μ := by
  set b : H → ℂ := realStandardMatrixCoefficient es ℓ f with hb
  obtain ⟨N, hN⟩ := RealPrincipalSeries.compactFunctionalGrowth (t + 1)
    (RealPrincipalSeries.expand es) ℓ hℓ
  obtain ⟨C, hC, hbound⟩ := hN (RealPrincipalSeries.expandedSmoothInclusion (t + 1) es f)
  have hbc : Continuous b :=
    RealPrincipalSeries.continuous_translate_coefficient (t + 1) (RealPrincipalSeries.expand es)
      ℓ hℓ _
  have hb_le : ∀ g, ‖b g‖ ≤ C * realMatrixHeight g ^ N := fun g => hbound g
  have hchar : Continuous fun g : H => ((charData e 0).character (determinant g) : ℂ) :=
    (Units.continuous_val.comp ((charData e 0).character.continuous.comp
      (Matrix.GeneralLinearGroup.continuous_det)))
  let f₁ : H → ℂ := fun g => ((charData e 0).character (determinant g) : ℂ) * b g
  let f₂ : H → ℂ := fun g => ((charData e 0).character (determinant g) : ℂ) * b (ιT g)
  have hf₁ : Measurable f₁ := (hchar.mul hbc).measurable
  have hf₂ : Measurable f₂ :=
    (hchar.mul (hbc.comp (GeneralLinear.continuous_inverseTranspose (t + 2) ℝ))).measurable
  have hf₁_le : ∀ g, ‖f₁ g‖ ≤ C * realMatrixHeight g ^ N := by
    intro g
    simp only [f₁, norm_mul, norm_charData_zero_character, one_mul]
    exact hb_le g
  have hf₂_le : ∀ g, ‖f₂ g‖ ≤ C * realMatrixHeight g ^ N := by
    intro g
    simp only [f₂, norm_mul, norm_charData_zero_character, one_mul]
    rw [← RealJacquet.realMatrixHeight_inverseTranspose g]
    exact hb_le (ιT g)
  obtain ⟨-, hI₁, -⟩ := Langlands.GodementJacquet.realMatrixInitialConvergence (r := t + 1) μ f₁ Ψ
    C N hf₁ hC hf₁_le
  obtain ⟨-, hI₂, -⟩ := Langlands.GodementJacquet.realMatrixInitialConvergence (r := t + 1) μ f₂
    Ψ' C N hf₂ hC hf₂_le
  refine ⟨((t + 1 : ℕ) : ℝ) + 1 + 2 * N - (m : ℝ) / 2, fun w hw => ⟨?_, ?_⟩⟩
  · have hre : ((t + 1 : ℕ) : ℝ) + 1 + 2 * N ≤ (w + (m : ℂ) / 2).re := by
      simp only [Complex.add_re, Complex.div_re, Complex.natCast_re]
      norm_num
      push_cast at hw ⊢
      linarith
    refine (hI₁ _ hre).congr (Eventually.of_forall fun g => ?_)
    exact (weightedMatrixTest_mul_eq e Ψ b _ g).symm
  · have hre : ((t + 1 : ℕ) : ℝ) + 1 + 2 * N ≤ (w + (m : ℂ) / 2).re := by
      simp only [Complex.add_re, Complex.div_re, Complex.natCast_re]
      norm_num
      push_cast at hw ⊢
      linarith
    refine (hI₂ _ hre).congr (Eventually.of_forall fun g => ?_)
    exact (weightedMatrixTest_mul_eq e Ψ' (b ∘ ιT) _ g).symm

variable (t) in
/-- For a linear form `ℓ` with a finite compact derivative bound on the smooth position principal
series of `expand es`, a standard vector `f`, a parity `e` and two square Schwartz tests `Ψ`,
`Ψ'`, the weighted matrix integrands of `Ψ` with `b(g) = ℓ(π(g) f)` and of `Ψ'` with `b ∘ ιT`
are integrable for every Haar measure on a common right half-plane. -/
def RealWeightedMatrixIntegrabilityStatement : Prop :=
  ∀ (μ : Measure H) [μ.IsHaarMeasure] (e : Fin 2) (es : List RealBlock)
    (ℓ : principalSeries ℝ (t + 2) (realPositionCharacter (RealPrincipalSeries.expand es)) →ₗ[ℂ] ℂ),
    RealPrincipalSeries.HasCompactDerivativeBound (t + 1) (RealPrincipalSeries.expand es) ℓ →
    ∀ (f : Automorphic.realStandardKFinite (t + 2) es) (Ψ Ψ' : 𝓢(Y, ℂ)),
    ∃ β : ℝ, ∀ w : ℂ, β < w.re →
      Integrable (fun g => realWeightedMatrixTest (charData e 0) Ψ (w + (m : ℂ) / 2) g *
        realStandardMatrixCoefficient es ℓ f g) μ ∧
      Integrable (fun g => realWeightedMatrixTest (charData e 0) Ψ' (w + (m : ℂ) / 2) g *
        realStandardMatrixCoefficient es ℓ f (ιT g)) μ

theorem realWeightedMatrixIntegrability : RealWeightedMatrixIntegrabilityStatement t :=
  fun μ _ e es ℓ hℓ f Ψ Ψ' => exists_realWeightedMatrix_integrable μ e es ℓ hℓ f Ψ Ψ'

end RealGodement

end Langlands.Global.RankinSelbergGlobal
