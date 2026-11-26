import Langlands.Global.RankinSelberg.RealMatrixCoefficientIntegrability
import Langlands.Global.RankinSelberg.RealMatrixOrbitIntegral
import Langlands.Global.RankinSelberg.RealPrincipalSeriesSmoothCoefficient

/-! # Passing weighted orbit evaluation identities through compact derivative functionals -/

noncomputable section

open Langlands.Archimedean Langlands.LocalFactor.Archimedean
open MeasureTheory Filter Set
open scoped Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealPrincipalSeries

open RealPlaceRestriction

local instance realCompGLMeasurable (n : ℕ) : MeasurableSpace (Langlands.GeneralLinear n ℝ) := borel _
local instance realCompGLBorel (n : ℕ) : BorelSpace (Langlands.GeneralLinear n ℝ) := ⟨rfl⟩
local instance realCompMatSecondCountable (n : ℕ) :
    SecondCountableTopology (Matrix (Fin n) (Fin n) ℝ) :=
  inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℝ))
local instance realCompGLSecondCountable (n : ℕ) : SecondCountableTopology (Langlands.GeneralLinear n ℝ) :=
  Units.isOpenEmbedding_val.isInducing.secondCountableTopology

variable {r : ℕ} {ds : List RealBlock}
local notation "n" => r + 1
local notation "G" => Langlands.GeneralLinear n ℝ
local notation "Mat" => Matrix (Fin n) (Fin n) ℝ
local notation "P" => principalSeries ℝ n (realPositionCharacter ds)
local notation "Kc" => unitaryCompact ℝ n
local notation "H" => @realMatrixHeight n
local notation "word" => RealLocalWhittaker.iteratedRightDerivative r

private def derivativeCoordinate (Xs : List Mat) : P →ₗ[ℂ] C(Kc, ℂ) where
  toFun f := ⟨fun k => word Xs f k.val,
    (RealUniformWhittaker.contMDiff_iteratedRightDerivative f.2.1 Xs).continuous.comp continuous_subtype_val⟩
  map_add' f f' := by
    ext1 k
    exact congrFun (RealUniformWhittaker.iteratedRightDerivative_add f.2.1 f'.2.1 Xs) k.val
  map_smul' c f := by
    ext1 k
    exact congrFun (RealUniformWhittaker.iteratedRightDerivative_smul f.2.1 c Xs) k.val

private def derivativeCoordinates {m : ℕ} (Xs : Fin m → List Mat) : P →ₗ[ℂ] (Fin m → C(Kc, ℂ)) :=
  LinearMap.pi fun i => derivativeCoordinate (Xs i)

private theorem continuous_derivativeCoordinates_orbit {m : ℕ} (Xs : Fin m → List Mat) (f : P) :
    Continuous (fun g : G => derivativeCoordinates Xs (translate r ds g f)) := by
  apply continuous_pi
  intro i
  apply ContinuousMap.continuous_of_continuous_uncurry
  let v (p : G × Kc) : G × G := (p.1, p.2.val)
  have hv₁ : Continuous (fun p : G × Kc => p.1) := continuous_fst
  have hv₂ : Continuous (fun p : G × Kc => p.2) := continuous_snd
  have hvK : Continuous (fun k : Kc => k.val) := continuous_subtype_val
  have hv : Continuous v := hv₁.prodMk (hvK.comp hv₂)
  change Continuous ((fun p : G × G => orbitWord r ds (Xs i) f p.1 p.2) ∘ v)
  exact (continuous_orbitWord r ds (Xs i) f).comp hv

private theorem exists_coordinate_factor {V E : Type*} [AddCommGroup V] [Module ℂ V]
    [NormedAddCommGroup E] [NormedSpace ℂ E] (J : V →ₗ[ℂ] E) (ℓ : V →ₗ[ℂ] ℂ)
    {A : ℝ} (h : ∀ v, ‖ℓ v‖ ≤ A * ‖J v‖) :
    ∃ L : E →L[ℂ] ℂ, ∀ v, L (J v) = ℓ v := by
  have hker : J.ker ≤ ℓ.ker := by
    intro v hv
    rw [LinearMap.mem_ker] at hv ⊢
    have hz : ‖ℓ v‖ ≤ 0 := by simpa only [hv, norm_zero, mul_zero] using h v
    exact norm_eq_zero.mp (le_antisymm hz (norm_nonneg _))
  let T := J.ker.liftQ ℓ hker ∘ₗ J.quotKerEquivRange.symm.toLinearMap
  have hT (v : V) : T (J.rangeRestrict v) = ℓ v := by
    change J.ker.liftQ ℓ hker (J.quotKerEquivRange.symm ⟨J v, ⟨v, rfl⟩⟩) = _
    rw [J.quotKerEquivRange_symm_apply_image]
    rfl
  have hTn (y : J.range) : ‖T y‖ ≤ A * ‖y‖ := by
    obtain ⟨v, hv⟩ := y.2
    have he : J.rangeRestrict v = y := Subtype.ext hv
    rw [← he, hT]
    exact h v
  obtain ⟨L, hL, _⟩ := exists_extension_norm_eq J.range (T.mkContinuous A hTn)
  exact ⟨L, fun v => (hL (J.rangeRestrict v)).trans (hT v)⟩

private theorem exists_derivativeCoordinate_factor (ℓ : P →ₗ[ℂ] ℂ)
    (hℓ : HasCompactDerivativeBound r ds ℓ) :
    ∃ (m : ℕ) (Xs : Fin m → List Mat) (L : (Fin m → C(Kc, ℂ)) →L[ℂ] ℂ),
      ∀ f, L (derivativeCoordinates Xs f) = ℓ f := by
  obtain ⟨m, Xs, A, _, hA⟩ := hℓ
  let J := derivativeCoordinates (ds := ds) Xs
  have hJ (f : P) : ‖ℓ f‖ ≤ (A * (m : ℝ)) * ‖J f‖ := by
    have hnorm := hA f (fun _ => ‖J f‖) fun i k hk =>
      ((J f i).norm_coe_le_norm ⟨k, hk⟩).trans (norm_le_pi_norm (J f) i)
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_assoc]
      using hnorm
  obtain ⟨L, hL⟩ := exists_coordinate_factor J ℓ hJ
  exact ⟨m, Xs, L, hL⟩

/-- Compact derivative bounds imply continuity of the coefficient of each orbit. -/
theorem continuous_compactFunctionalCoefficient (ℓ : P →ₗ[ℂ] ℂ)
    (hℓ : HasCompactDerivativeBound r ds ℓ) (f : P) :
    Continuous (fun g : G => ℓ (translate r ds g f)) :=
  continuous_translate_coefficient r ds ℓ hℓ f

private theorem exists_derivativeCoordinates_bound {m : ℕ} (Xs : Fin m → List Mat) (f : P) :
    ∃ (B : ℝ) (p : ℕ), 0 ≤ B ∧ ∀ g : G, ‖derivativeCoordinates Xs (translate r ds g f)‖ ≤ B * H g ^ p := by
  classical
  obtain ⟨N, hN⟩ := exists_uniform_orbitWord_height r ds
  choose C hC hc using fun i : Fin m => hN (Xs i) f
  have hHK : Continuous (fun k : Kc => H k.val) := continuous_realMatrixHeight.comp continuous_subtype_val
  obtain ⟨A, hA⟩ := isCompact_univ.exists_bound_of_continuousOn hHK.continuousOn
  let B₀ := max A 1
  let B := ∑ i : Fin m, C i * B₀ ^ N
  let p := N + ∑ i, (Xs i).length
  have hB₀ : 0 ≤ B₀ := zero_le_one.trans (le_max_right _ _)
  have hB : 0 ≤ B := Finset.sum_nonneg fun i _ => mul_nonneg (hC i) (pow_nonneg hB₀ _)
  refine ⟨B, p, hB, fun g => ?_⟩
  have hg := realMatrixHeight_nonneg g
  have hp : 0 ≤ B * H g ^ p := mul_nonneg hB (pow_nonneg hg _)
  apply (pi_norm_le_iff_of_nonneg hp).2
  intro i
  apply (ContinuousMap.norm_le _ hp).2
  intro k
  have hk : H k.val ≤ B₀ := (Real.le_norm_self _).trans ((hA k (mem_univ _)).trans (le_max_left _ _))
  have hCk : C i * H k.val ^ N ≤ B :=
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (realMatrixHeight_nonneg k.val) hk _) (hC i)).trans
      (Finset.single_le_sum (fun j _ => mul_nonneg (hC j) (pow_nonneg hB₀ _)) (Finset.mem_univ i))
  have hp' : N + (Xs i).length ≤ p := Nat.add_le_add_left
    (Finset.single_le_sum (fun j _ => Nat.zero_le (Xs j).length) (Finset.mem_univ i)) N
  have hg' : 1 ≤ H g := (by norm_num : (1 : ℝ) ≤ 2).trans (two_le_realMatrixHeight (Nat.succ_pos r) g)
  exact (hc i g k.val).trans (mul_le_mul hCk (pow_le_pow_right₀ hg' hp') (pow_nonneg hg _) hB)

private theorem integrable_smul_derivativeCoordinates (μ : Measure G) {W : G → ℂ}
    (hW : AEStronglyMeasurable W μ) (hI : ∀ p : ℕ, Integrable (fun g => ‖W g‖ * H g ^ p) μ)
    {τ : G → G} (hτ : Continuous τ) (hτH : ∀ g, H (τ g) = H g)
    {m : ℕ} (Xs : Fin m → List Mat) (f : P) :
    Integrable (fun g => W g • derivativeCoordinates Xs (translate r ds (τ g) f)) μ := by
  obtain ⟨B, p, _, hb⟩ := exists_derivativeCoordinates_bound Xs f
  let : SecondCountableTopologyEither G (Fin m → C(Kc, ℂ)) :=
    ⟨Or.inl (realCompGLSecondCountable n)⟩
  have hc : Continuous (fun g : G => derivativeCoordinates Xs (translate r ds (τ g) f)) :=
    (continuous_derivativeCoordinates_orbit Xs f).comp hτ
  refine ((hI p).const_mul B).mono' (hW.smul hc.aestronglyMeasurable) (ae_of_all μ fun g => ?_)
  rw [norm_smul]
  have hg := hb (τ g)
  rw [hτH] at hg
  calc
    _ ≤ ‖W g‖ * (B * H g ^ p) := mul_le_mul_of_nonneg_left hg (norm_nonneg _)
    _ = _ := by ring

/-- Transfer an equality of weighted evaluations to any compact-derivative-bounded linear form. -/
theorem integral_compactFunctional_eq_of_evaluation_eq (μ : Measure G) {W W' : G → ℂ}
    (hW : AEStronglyMeasurable W μ) (hW' : AEStronglyMeasurable W' μ)
    (hI : ∀ m : ℕ, Integrable (fun g => ‖W g‖ * H g ^ m) μ)
    (hI' : ∀ m : ℕ, Integrable (fun g => ‖W' g‖ * H g ^ m) μ)
    {τ τ' : G → G} (hτ : Continuous τ) (hτ' : Continuous τ')
    (hτH : ∀ g, H (τ g) = H g) (hτH' : ∀ g, H (τ' g) = H g) (f : P)
    (ℓ : P →ₗ[ℂ] ℂ) (hℓ : HasCompactDerivativeBound r ds ℓ)
    (hE : ∀ x : G, (∫ g, W g * (f : G → ℂ) (x * τ g) ∂μ) =
      ∫ g, W' g * (f : G → ℂ) (x * τ' g) ∂μ) :
    (∫ g, W g * ℓ (translate r ds (τ g) f) ∂μ) = ∫ g, W' g * ℓ (translate r ds (τ' g) f) ∂μ := by
  obtain ⟨m, Xs, L, hL⟩ := exists_derivativeCoordinate_factor ℓ hℓ
  let B (g : G) := W g • derivativeCoordinates Xs (translate r ds (τ g) f)
  let B' (g : G) := W' g • derivativeCoordinates Xs (translate r ds (τ' g) f)
  have hB : Integrable B μ := integrable_smul_derivativeCoordinates μ hW hI hτ hτH Xs f
  have hB' : Integrable B' μ := integrable_smul_derivativeCoordinates μ hW' hI' hτ' hτH' Xs f
  have hev := integral_orbitWord_eq_of_evaluation_eq μ hW hW' hI hI' hτ hτ' hτH hτH' f hE
  have hvec : (∫ g, B g ∂μ) = ∫ g, B' g ∂μ := by
    funext i
    ext1 k
    let E : (Fin m → C(Kc, ℂ)) →L[ℂ] ℂ := (ContinuousMap.evalCLM (R := ℂ) k).comp (ContinuousLinearMap.proj i)
    change E (∫ g, B g ∂μ) = E (∫ g, B' g ∂μ)
    rw [← E.integral_comp_comm hB, ← E.integral_comp_comm hB']
    exact hev (Xs i) k.val
  have hBℓ (g : G) : L (B g) = W g * ℓ (translate r ds (τ g) f) := by
    simp only [B, map_smul, hL, smul_eq_mul]
  have hB'ℓ (g : G) : L (B' g) = W' g * ℓ (translate r ds (τ' g) f) := by
    simp only [B', map_smul, hL, smul_eq_mul]
  simp_rw [← hBℓ, ← hB'ℓ]
  rw [L.integral_comp_comm hB, L.integral_comp_comm hB', hvec]

end Langlands.Global.RankinSelbergGlobal.RealPrincipalSeries
