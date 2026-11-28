import Langlands.Global.RankinSelberg.RealSquarePolynomialGaussian
import Langlands.Global.RankinSelberg.RealTriangularAdditiveDiagonal
import Langlands.Representation.Archimedean.RealInductionStagesSlice

/-! # Polynomial normalization of the real square zeta integral -/

noncomputable section

open Complex MeasureTheory MvPolynomial
open scoped Matrix.Norms.Operator SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.GodementJacquet

open Langlands.Archimedean Langlands.GeneralLinear
open Langlands.Archimedean.RealJacquetFrobenius (charFun charFun_mul_cpow)
open Langlands.Archimedean.InductionStages (integral_mem)
open Langlands.Global.RankinSelbergGlobal
open ArchimedeanLocal
open ArchimedeanDeterminantTheta
open RealGodementGaussianPolynomial (Coordinates)
open RealSquarePolynomialGaussian (squarePolynomialGaussian realSquarePolynomialMarginal)

local instance squarePolynomialGLMeasurable (j : ℕ) : MeasurableSpace (GeneralLinear j ℝ) := borel _
local instance squarePolynomialGLBorel (j : ℕ) : BorelSpace (GeneralLinear j ℝ) := ⟨rfl⟩
local instance squarePolynomialUnitsMeasurable : MeasurableSpace ℝˣ := borel _
local instance squarePolynomialUnitsBorel : BorelSpace ℝˣ := ⟨rfl⟩
local instance squarePolynomialDiagonalSigmaFinite (n : ℕ) : SigmaFinite (realDiagonalHaar n) := by
  unfold realDiagonalHaar
  infer_instance

variable {r : ℕ}
local notation "n" => r + 1
local notation "I" => Fin n
local notation "Mat" => Matrix I I ℝ
local notation "K" => unitaryCompact ℝ n
local notation "G" => GeneralLinear n ℝ
local notation "D" => I → ℝˣ

private theorem integral_realDiagonalWeighted_shift (χ : ℕ → ℝˣ → ℂ) (e : I → Fin 2) (u : I → ℂ)
    (hχ : ∀ (i : I) (x : ℝˣ), χ i x = charFun (e i) (u i) x)
    (F : (I → ℝ) → ℂ) (hF : Measurable F) (v s : ℂ) :
    (∫ d, realDiagonalWeightedIntegrand χ v F (fun x => (x : ℂ) ^ s) d ∂realDiagonalHaar n) =
      v * ∫ x, weightedKernel e (fun i => s + u i) F x := by
  have hD (d : D) : realDiagonalWeightedIntegrand χ v F (fun x => (x : ℂ) ^ s) d =
      v * (F (fun i => (d i : ℝ)) * ∏ i, charFun (e i) (s + u i) (d i : ℝ)) := by
    simp only [realDiagonalWeightedIntegrand, realDiagonalZetaWeight_eq, zero_mul, exp_zero, mul_one,
      hχ, realDiagonalAbs]
    rw [Langlands.Archimedean.InductionStages.cpow_prod_ofReal _ _ (fun _ => abs_nonneg _) _]
    have hChar (i : I) : charFun (e i) (u i) (d i : ℝ) * ((|(d i : ℝ)| : ℝ) : ℂ) ^ s =
        charFun (e i) (s + u i) (d i : ℝ) := by
      rw [charFun_mul_cpow _ _ _ (d i).ne_zero, add_comm (u i) s]
    rw [← show (∏ i, charFun (e i) (u i) (d i : ℝ)) * (∏ i, ((|(d i : ℝ)| : ℝ) : ℂ) ^ s) =
        ∏ i, charFun (e i) (s + u i) (d i : ℝ) by
      rw [← Finset.prod_mul_distrib]; exact Finset.prod_congr rfl fun i _ => hChar i]
    ring
  simp_rw [hD, integral_const_mul]
  exact congrArg (v * ·) (realDiagonalTateIntegration n e (fun i => s + u i) F hF).2

private def diagonalGaussianSpectral {β : ℝ} (e : I → Fin 2) (u : I → ℂ)
    (hβ : ∀ s : ℂ, β < s.re → ∀ i, 0 < (s + u i).re) :
    MvPolynomial I ℂ →ₗ[ℂ] ({s : ℂ // β < s.re} → ℂ) where
  toFun P s := ∫ x, weightedKernel e (fun i => s.val + u i) (diagonalPolynomialGaussian P) x
  map_add' P Q := by
    funext s
    have hI (R : MvPolynomial I ℂ) : Integrable
        (weightedKernel e (fun i => s.val + u i) (diagonalPolynomialGaussian R)) := by
      obtain ⟨B, hB⟩ := realDiagonalPolynomialGaussian n R e u
      exact (hB s (hβ s s.2)).1
    simp only [Pi.add_apply]
    rw [← integral_add (hI P) (hI Q)]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only [weightedKernel, diagonalPolynomialGaussian, map_add, add_mul]
  map_smul' c P := by
    funext s
    simp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul, ← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only [weightedKernel, diagonalPolynomialGaussian, MvPolynomial.smul_eq_C_mul,
      map_mul, eval_C, mul_assoc]

/-- A standard polynomial Gaussian square test and a real principal-series vector give a
polynomial times the product of their specified real Tate factors on an initial right
half-plane of absolute convergence. -/
def RealSquareZetaPolynomialStatement : Prop :=
  ∀ (r : ℕ) (μ : Measure (GeneralLinear (r + 1) ℝ)) [μ.IsHaarMeasure]
    (κ : Measure (unitaryCompact ℝ (r + 1))) [κ.IsHaarMeasure] [SFinite κ]
    (χ : ℕ → ℝˣ → ℂ) (e : Fin (r + 1) → Fin 2) (u : Fin (r + 1) → ℂ),
    (∀ (i : Fin (r + 1)) (x : ℝˣ), χ i x = charFun (e i) (u i) x) →
    ∀ (f : GeneralLinear (r + 1) ℝ → ℂ), f ∈ principalSeries ℝ (r + 1) χ →
    ∀ (Φ : 𝓢(Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ, ℂ)) (P : MvPolynomial (Coordinates (r + 1) (r + 1)) ℂ),
      (Φ : Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ → ℂ) = squarePolynomialGaussian P →
      (∃ β : ℝ, ∀ s : ℂ, β < s.re → Integrable
        (realMatrixWeightedIntegrand f Φ (fun x => (x : ℂ) ^ s)) μ) →
      ∃ (β : ℝ) (Q : Polynomial ℂ), ∀ s : ℂ, β < s.re →
        let Z := realMatrixWeightedIntegrand f Φ (fun x => (x : ℂ) ^ s)
        Integrable Z μ ∧ (∫ g, Z g ∂μ) = Q.eval s * ∏ i, Gammaℝ (s + u i + (e i).val)

set_option maxHeartbeats 1000000 in
theorem realSquareZetaPolynomial : RealSquareZetaPolynomialStatement := by
  intro r μ _ κ _ _ χ e u hχ f hf Φ P hΦ ⟨σ, hσ⟩
  let β := max σ (∑ i, |(u i).re|)
  have hβ (s : ℂ) (hs : β < s.re) (i : Fin (r + 1)) : 0 < (s + u i).re := by
    have hsum := (le_max_right σ (∑ j, |(u j).re|)).trans_lt hs
    have hi := Finset.single_le_sum (f := fun j => |(u j).re|) (fun j _ => abs_nonneg ((u j).re))
      (Finset.mem_univ i)
    rw [add_re]
    linarith [neg_abs_le (u i).re]
  let S := {s : ℂ // β < s.re}
  let H (s : ℂ) (x : ℝ) := (x : ℂ) ^ s
  let L := diagonalGaussianSpectral e u hβ
  let V := (restrictTotalDegree (Fin (r + 1)) ℂ P.totalDegree).map L
  let A (s : S) (p : unitaryCompact ℝ (r + 1) × (Fin (r + 1) → ℝˣ)) :=
    realDiagonalWeightedIntegrand χ (f p.1.val) (realTriangularMarginal 1 Φ p.1) (H s) p.2
  let Y (k : unitaryCompact ℝ (r + 1)) (s : S) := ∫ d, A s (k, d) ∂realDiagonalHaar (r + 1)
  obtain ⟨c, _, hc⟩ := realTriangularMatched (r := r) μ κ 1
  have hI (s : S) : Integrable (realMatrixWeightedIntegrand f Φ (H s)) μ :=
    hσ s ((le_max_left σ _).trans_lt s.2)
  have hA (s : S) := (hc χ f hf Φ (H s) (by dsimp [H]; fun_prop)).1 (hI s)
  have hY (s : S) : Integrable (fun k => Y k s) κ := (hA s).1.integral_prod_left
  have hV (k : unitaryCompact ℝ (r + 1)) : Y k ∈ V := by
    obtain ⟨Q, hQ, hTest⟩ := realSquarePolynomialMarginal r Φ P hΦ k
    have hmem : Q ∈ restrictTotalDegree (Fin (r + 1)) ℂ P.totalDegree :=
      (mem_restrictTotalDegree _ _ _).mpr hQ
    have hEq : Y k = f k.val • L Q := by
      funext s
      change (∫ d, realDiagonalWeightedIntegrand χ (f k.val) (realTriangularMarginal 1 Φ k)
        (H s) d ∂realDiagonalHaar (r + 1)) = f k.val * L Q s
      rw [integral_realDiagonalWeighted_shift χ e u hχ _
        (realTriangularMarginal 1 Φ k).continuous.measurable, hTest]
      rfl
    rw [hEq]
    exact Submodule.smul_mem V _ ⟨Q, hmem, rfl⟩
  obtain ⟨Q, _, hQ⟩ := integral_mem κ V hV hY
  obtain ⟨p, hp⟩ := realDiagonalPolynomialGaussian (r + 1) Q e u
  refine ⟨β, Polynomial.C (c : ℂ) * p, fun s hs => ⟨hI ⟨s, hs⟩, ?_⟩⟩
  have hEq := (hA ⟨s, hs⟩).2
  rw [integral_prod _ (hA ⟨s, hs⟩).1] at hEq
  change (∫ g, realMatrixWeightedIntegrand f Φ (H s) g ∂μ) = (c : ℂ) * ∫ k, Y k ⟨s, hs⟩ ∂κ at hEq
  rw [hEq, ← congrFun hQ ⟨s, hs⟩]
  change (c : ℂ) * (∫ x, weightedKernel e (fun i => s + u i) (diagonalPolynomialGaussian Q) x) = _
  rw [(hp s (hβ s hs)).2, Polynomial.eval_mul, Polynomial.eval_C, mul_assoc]

end Langlands.GodementJacquet
