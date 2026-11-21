import Langlands.Global.RankinSelberg.RealLocalEqualUnfolding
import Langlands.Global.RankinSelberg.RealGodementRectangularFourier

/-! # Real square Schwartz tests and their row-factor Fourier identity -/

noncomputable section

open Langlands.HarmonicAnalysis Langlands.LocalFactor.Archimedean
open Langlands.RankinSelberg (rectangularMeasure)
open MeasureTheory
open scoped ContDiff SchwartzMap Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealGodement

open ArchimedeanLocal

private theorem norm_deriv_comp_le {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E →L[ℝ] F) (hL : ‖L‖ ≤ 1) (f : 𝓢(F, ℂ)) (j : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ j (f ∘ L) x‖ ≤ ‖iteratedFDeriv ℝ j f (L x)‖ := by
  rw [L.iteratedFDeriv_comp_right (f.smooth ⊤) x (by simp)]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hL)

private def complexSchwartzProduct {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (f : 𝓢(E, ℂ)) (g : 𝓢(F, ℂ)) : 𝓢(E × F, ℂ) where
  toFun p := f p.1 * g p.2
  smooth' := (f.smooth'.comp contDiff_fst).mul (g.smooth'.comp contDiff_snd)
  decay' k n := by
    let L := ContinuousLinearMap.fst ℝ E F
    let M := ContinuousLinearMap.snd ℝ E F
    let f₁ := (f : E → ℂ) ∘ L
    let g₂ := (g : F → ℂ) ∘ M
    have hf : ContDiff ℝ ∞ f₁ := f.smooth'.comp L.contDiff
    have hg : ContDiff ℝ ∞ g₂ := g.smooth'.comp M.contDiff
    refine ⟨∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
      (SchwartzMap.seminorm ℝ k i f * SchwartzMap.seminorm ℝ 0 (n - i) g +
        SchwartzMap.seminorm ℝ 0 i f * SchwartzMap.seminorm ℝ k (n - i) g), fun p => ?_⟩
    calc
      _ ≤ ‖p‖ ^ k * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i f₁ p‖ * ‖iteratedFDeriv ℝ (n - i) g₂ p‖ :=
        mul_le_mul_of_nonneg_left (norm_iteratedFDeriv_mul_le hf hg p (by simp)) (by positivity)
      _ ≤ _ := by
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro i _
        have h₁ := norm_deriv_comp_le L (ContinuousLinearMap.norm_fst_le ℝ E F) f i p
        have h₂ := norm_deriv_comp_le M (ContinuousLinearMap.norm_snd_le ℝ E F) g (n - i) p
        have hB₁ := SchwartzMap.norm_iteratedFDeriv_le_seminorm ℝ f i p.1
        have hB₂ := SchwartzMap.norm_iteratedFDeriv_le_seminorm ℝ g (n - i) p.2
        have hx := SchwartzMap.le_seminorm ℝ k i f p.1
        have hy := SchwartzMap.le_seminorm ℝ k (n - i) g p.2
        change ‖iteratedFDeriv ℝ i f₁ p‖ ≤ ‖iteratedFDeriv ℝ i f p.1‖ at h₁
        change ‖iteratedFDeriv ℝ (n - i) g₂ p‖ ≤ ‖iteratedFDeriv ℝ (n - i) g p.2‖ at h₂
        have hb (w : ℝ) (hw : 0 ≤ w) :
            w * (↑(n.choose i) * ‖iteratedFDeriv ℝ i f₁ p‖ * ‖iteratedFDeriv ℝ (n - i) g₂ p‖) ≤
              (n.choose i : ℝ) * (w * ‖iteratedFDeriv ℝ i f p.1‖ * ‖iteratedFDeriv ℝ (n - i) g p.2‖) := by
          rw [show w * (↑(n.choose i) * ‖iteratedFDeriv ℝ i f₁ p‖ * ‖iteratedFDeriv ℝ (n - i) g₂ p‖) =
              (n.choose i : ℝ) * (w * ‖iteratedFDeriv ℝ i f₁ p‖ * ‖iteratedFDeriv ℝ (n - i) g₂ p‖) by ring]
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul (mul_le_mul_of_nonneg_left h₁ hw) h₂ (norm_nonneg _) (by positivity)) (by positivity)
        refine (hb _ (by positivity)).trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
        by_cases h : ‖p.1‖ ≤ ‖p.2‖
        · rw [Prod.norm_def, max_eq_right h, mul_comm (‖p.2‖ ^ k), mul_assoc]
          exact (mul_le_mul hB₁ hy (by positivity) (by positivity)).trans (le_add_of_nonneg_left (by positivity))
        · rw [Prod.norm_def, max_eq_left (le_of_not_ge h)]
          exact (mul_le_mul hx hB₂ (norm_nonneg _) (by positivity)).trans (le_add_of_nonneg_right (by positivity))

variable {t : ℕ}

local notation "m" => (t + 1)
local notation "n" => (t + 2)
local notation "Y" => Matrix (Fin (t + 2)) (Fin (t + 2)) ℝ
local notation "X" => Matrix (Fin (t + 1)) (Fin (t + 2)) ℝ
local notation "Row" => (Fin (t + 2) → ℝ)

variable (t) in
private def squareRows : Y ≃L[ℝ] Row × X :=
  ({ toEquiv := (Fin.snocEquiv (fun _ : Fin n => Row)).symm
     map_add' := fun _ _ => rfl
     map_smul' := fun _ _ => rfl } : Y ≃ₗ[ℝ] Row × X).toContinuousLinearEquiv

/-- The product of the two tests in (8.1), as a Schwartz function on square matrices. -/
def equalSquareSchwartz (Φ : 𝓢(X, ℂ)) (φ : 𝓢(Row, ℂ)) : 𝓢(Y, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (squareRows t) (complexSchwartzProduct φ Φ)

@[simp]
theorem equalSquareSchwartz_apply (Φ : 𝓢(X, ℂ)) (φ : 𝓢(Row, ℂ)) (A : Y) :
    equalSquareSchwartz Φ φ A = equalSquareTest Φ φ A := mul_comm _ _

/-- The Fourier integral of the product separates into the first rows and the
last row, with the same positive kernel and entrywise self-dual measure. -/
theorem equalSquareFourierIntegral (b : ℝˣ) (Φ : X → ℂ) (φ : Row → ℂ) (B : Y) :
    rectangularFourierIntegral (realScaledCharacter b) (realSelfDualMeasure b) (equalSquareTest Φ φ) B =
      rectangularFourierIntegral (realScaledCharacter b) (realSelfDualMeasure b) Φ (squareFirstRows B) *
        realFourierTransform b φ (B (Fin.last m)) := by
  let ν := realSelfDualMeasure b
  let ψ := realScaledCharacter b
  let : ν.measure.IsAddHaarMeasure := ν.isAddHaar
  let η : Measure Row := Measure.pi (fun _ : Fin n => ν.measure)
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin n => Row) (Fin.last m)
  have hm : MeasurePreserving e (rectangularMeasure ν n n) (η.prod (rectangularMeasure ν m n)) :=
    measurePreserving_piFinSuccAbove (fun _ : Fin n => η) (Fin.last m)
  let f (x : Row) := φ x * ψ.complex (∑ j, x j * B (Fin.last m) j)
  let F (A : X) := Φ A * ψ.complex (rectangularPairing A (squareFirstRows B))
  let J (A : Y) := equalSquareTest Φ φ A * ψ.complex (rectangularPairing A B)
  have hlast (p : Row × X) : e.symm p (Fin.last m) = p.1 := by
    simp [e, MeasurableEquiv.piFinSuccAbove, Fin.snocEquiv]
  have htop (p : Row × X) (i : Fin m) : e.symm p i.castSucc = p.2 i := by
    simpa only [Fin.succAbove_last] using
      (show e.symm p ((Fin.last m).succAbove i) = p.2 i by
        simp [e, MeasurableEquiv.piFinSuccAbove, Fin.snocEquiv])
  have hTest (p : Row × X) : J (e.symm p) = f p.1 * F p.2 := by
    have hRows : squareFirstRows (e.symm p) = p.2 := funext (htop p)
    have hPair : rectangularPairing (e.symm p) B =
        rectangularPairing p.2 (squareFirstRows B) + ∑ j, p.1 j * B (Fin.last m) j := by
      unfold rectangularPairing
      rw [Fin.sum_univ_castSucc]
      simp only [squareFirstRows, Matrix.submatrix_apply, id_eq, htop, hlast]
    simp only [J, equalSquareTest, f, F, hPair, hRows, hlast, AddChar.map_add_eq_mul]
    ring
  change (∫ A, J A ∂rectangularMeasure ν n n) = _
  calc
    _ = ∫ p, J (e.symm p) ∂η.prod (rectangularMeasure ν m n) := (hm.symm e).integral_comp' J |>.symm
    _ = ∫ p, f p.1 * F p.2 ∂η.prod (rectangularMeasure ν m n) := integral_congr_ae (.of_forall hTest)
    _ = (∫ x, f x ∂η) * ∫ A, F A ∂rectangularMeasure ν m n := integral_prod_mul _ _
    _ = _ := mul_comm _ _

variable (t) in
/-- Fourier transformation of the square test is the product of the rectangular
and last-row Fourier transforms at the same parameter. -/
def RealLocalEqualSquareFourierStatement : Prop :=
  ∀ (b : ℝˣ) (Φ : 𝓢(X, ℂ)) (φ : 𝓢(Row, ℂ)) (B : Y),
    realRectangularSchwartzFourier b (equalSquareSchwartz Φ φ) B =
      equalSquareTest (realRectangularSchwartzFourier b Φ) (realFourierTransform b φ) B

theorem realLocalEqualSquareFourier : RealLocalEqualSquareFourierStatement t := by
  intro b Φ φ B
  simp only [realRectangularSchwartzFourier_apply, show (equalSquareSchwartz Φ φ : Y → ℂ) =
      equalSquareTest Φ φ from funext (equalSquareSchwartz_apply Φ φ),
    equalSquareFourierIntegral, equalSquareTest]

end Langlands.Global.RankinSelbergGlobal.RealGodement
