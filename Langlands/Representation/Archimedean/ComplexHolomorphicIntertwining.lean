import Langlands.Representation.Archimedean.ComplexHolomorphicJets

/-!
# Holomorphic right derivatives act on jets by the operators `opDataH`

For characters `χ_k(z) = phase(z)^{l_k} |z|^{2 t_k}` and `F` in the principal series of `χ`, the
holomorphic right derivative `holDeriv X F = ½ (R(X) F - i R(iX) F)` satisfies
(`hasJet_holDeriv`): if `F` has jet `Q`, then `holDeriv X F` has jet
`op (opDataH α X) Q = Σ_p W_{X,p} ∂_{v_p} Q + λ_X Q` with `α_k = l_k/2 + t_k + (n-1)/2 - k`.
On the lower unipotent group `holDeriv X F = λ_X φ + ∂φ[W_X]` (`holDeriv_nbUnit`, from
`rightDerivative_nbMat`), and the weighted holomorphic derivative `wirt_weighted_apply` gives the
new formal polynomial; setting `v̄ = 0` kills every derivative of a Gram weight.
-/

noncomputable section

open scoped Matrix ComplexConjugate Matrix.Norms.Operator

set_option autoImplicit false

namespace Langlands.Archimedean.HolomorphicJets

open MvPolynomial Langlands.GeneralLinear Langlands.Archimedean.NoncompactPicture
open Langlands.Archimedean.MomentSymbols Langlands.Archimedean.RealPolynomialFunctions
open Langlands.Archimedean.AdjacentGrowth Langlands.Archimedean.LevelFunctions

set_option backward.isDefEq.respectTransparency false

variable {n : ℕ}

/-- The holomorphic right derivative `½ (R(X) - i R(iX))`. -/
def holDeriv (X : Matrix (Fin n) (Fin n) ℂ) (F : Langlands.GeneralLinear n ℂ → ℂ) :
    Langlands.GeneralLinear n ℂ → ℂ :=
  (2 : ℂ)⁻¹ • (rightDerivative (matrixModel ℂ n) X F -
    Complex.I • rightDerivative (matrixModel ℂ n) (Complex.I • X) F)

/-- The holomorphic torus coefficients. -/
def alphaOf (l : ℕ → ℤ) (t : ℕ → ℂ) (k : Fin n) : ℂ :=
  (l k : ℂ) / 2 + (t k + ((n : ℂ) - 1) / 2 - ((k : ℕ) : ℂ))

theorem conjMat_I_smul (X : Matrix (Fin n) (Fin n) ℂ) (v : Lw n → ℂ) :
    conjMat (Complex.I • X) v = Complex.I • conjMat X v := by
  simp [conjMat]

theorem fieldW_I_smul (X : Matrix (Fin n) (Fin n) ℂ) (v : Lw n → ℂ) :
    fieldW (Complex.I • X) v = Complex.I • fieldW X v := by
  have hl : lowMat (lowCoords (Complex.I • conjMat X v)) =
      Complex.I • lowMat (lowCoords (conjMat X v)) := by
    ext a b
    simp only [lowMat, lowCoords, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
    split_ifs <;> simp
  funext p
  simp only [fieldW, conjMat_I_smul, hl, Matrix.smul_mul, lowCoords, Matrix.smul_apply,
    Pi.smul_apply]

theorem torusDeriv_hol (l : ℕ → ℤ) (t : ℕ → ℂ) (d : Fin n → ℂ) :
    (2 : ℂ)⁻¹ * (torusDeriv l t d - Complex.I * torusDeriv l t (fun a => Complex.I * d a)) =
      ∑ k, alphaOf l t k * d k := by
  simp only [torusDeriv, alphaOf, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hre : (Complex.I * d k).re = -(d k).im := by simp
  have him : (Complex.I * d k).im = (d k).re := by simp
  rw [hre, him]
  conv_rhs => rw [← Complex.re_add_im (d k)]
  push_cast
  have := Complex.I_mul_I
  linear_combination (-(l k : ℂ) / 2 * ((d k).re : ℂ)) * this

/-! ## On the lower unipotent group -/

theorem differentiable_nbUnit_comp {χ : ℕ → ℂˣ → ℂ} {F : Langlands.GeneralLinear n ℂ → ℂ}
    (hF : F ∈ principalSeries ℂ n χ) : Differentiable ℝ fun w => F (nbUnit w) := by
  have hFs := ((mem_principalSeries_iff ℂ n χ F).1 hF).1
  intro v
  have hcomp : (fun w => F (nbUnit w)) = unitsExtension F ∘ fun w => 1 + lowMatCLM w := by
    funext w
    simp only [Function.comp_apply]
    rw [show (1 : Matrix (Fin n) (Fin n) ℂ) + lowMatCLM w = (nbUnit w : Matrix _ _ ℂ) from rfl,
      unitsExtension_val]
  rw [hcomp]
  exact (differentiableAt_unitsExtension hFs (isUnit_nbMat v)).comp v
    ((lowMatCLM.differentiableAt).const_add 1)

theorem rightDerivative_nbUnit {χ : ℕ → ℂˣ → ℂ} (l : ℕ → ℤ) (t : ℕ → ℂ)
    (hχ : ∀ k z, χ k z = phase z ^ l k * ((‖(z : ℂ)‖ : ℂ)) ^ (2 * t k))
    {F : Langlands.GeneralLinear n ℂ → ℂ} (hF : F ∈ principalSeries ℂ n χ)
    (X : Matrix (Fin n) (Fin n) ℂ) (v : Lw n → ℂ) :
    rightDerivative (matrixModel ℂ n) X F (nbUnit v) =
      torusDeriv l t (fun a => conjMat X v a a) * F (nbUnit v) +
        fderiv ℝ (fun w => F (nbUnit w)) v (fieldW X v) :=
  rightDerivative_nbMat hF (principalSeriesCharacter_one l t hχ) (torusDeriv l t)
    (fun d y => fderiv_unitsExtension_diagonal_mul l t hχ hF d y) X v

/-- **The holomorphic right derivative on the lower unipotent group.** -/
theorem holDeriv_nbUnit {χ : ℕ → ℂˣ → ℂ} (l : ℕ → ℤ) (t : ℕ → ℂ)
    (hχ : ∀ k z, χ k z = phase z ^ l k * ((‖(z : ℂ)‖ : ℂ)) ^ (2 * t k))
    {F : Langlands.GeneralLinear n ℂ → ℂ} (hF : F ∈ principalSeries ℂ n χ)
    (X : Matrix (Fin n) (Fin n) ℂ) (v : Lw n → ℂ) :
    holDeriv X F (nbUnit v) = (∑ k, alphaOf l t k * conjMat X v k k) * F (nbUnit v) +
      wirt (fun w => F (nbUnit w)) v (fieldW X v) := by
  have h1 := rightDerivative_nbUnit l t hχ hF X v
  have h2 := rightDerivative_nbUnit l t hχ hF (Complex.I • X) v
  rw [conjMat_I_smul, fieldW_I_smul] at h2
  simp only [Matrix.smul_apply, smul_eq_mul] at h2
  simp only [holDeriv, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, h1, h2]
  rw [← torusDeriv_hol, wirt]
  ring

/-! ## The intertwining -/

/-- The formal holomorphic derivative along `fieldWH X`. -/
def dW (X : Matrix (Fin n) (Fin n) ℂ) (P : R2 n) : R2 n :=
  ∑ k, holIncl (fieldWH X k) * pderiv (k, false) P

theorem evalC_dW (X : Matrix (Fin n) (Fin n) ℂ) (P : R2 n) (v : Lw n → ℂ) :
    evalC (dW X P) v = wirt (evalC P) v (fieldW X v) := by
  rw [wirt_evalC, dW, ← evalAt_apply, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, evalAt_apply, evalAt_apply, evalC_holIncl, eval_fieldWH, mul_comm]

theorem holPart_dW (X : Matrix (Fin n) (Fin n) ℂ) (P : R2 n) :
    holPart (dW X P) = ∑ k, fieldWH X k * pderiv k (holPart P) := by
  simp only [dW, map_sum, map_mul, holPart_holIncl, holPart_pderiv]

theorem holPart_dW_eq_zero_of {X : Matrix (Fin n) (Fin n) ℂ} {P : R2 n} (h : holPart P = 1) :
    holPart (dW X P) = 0 := by
  rw [holPart_dW, h]
  simp

theorem ιP_pderiv (k : Lw n) (h : Hol n) : ιP (pderiv k h) = pderiv (vV k) (ιP h) := by
  classical
  induction h using MvPolynomial.induction_on with
  | C a => simp
  | add f g hf hg => simp only [map_add, hf, hg]
  | mul_X f j hf =>
    rw [pderiv_mul, map_add, map_mul, map_mul, hf, map_mul, pderiv_mul, rename_X, pderiv_X,
      pderiv_X]
    by_cases hjk : j = k
    · subst hjk; simp
    · have : vV j ≠ vV k := fun h' => hjk (vV_injective h')
      simp [hjk, this]

theorem evalAt_C (v : Lw n → ℂ) (a : ℂ) : evalAt v (C a) = a := eval_C a

/-- **Holomorphic right derivatives act on jets by the operators `opDataH`.** -/
theorem hasJet_holDeriv {χ : ℕ → ℂˣ → ℂ} (l : ℕ → ℤ) (t : ℕ → ℂ)
    (hχ : ∀ k z, χ k z = phase z ^ l k * ((‖(z : ℂ)‖ : ℂ)) ^ (2 * t k)) {σ : Fin n → ℂ}
    {F : Langlands.GeneralLinear n ℂ → ℂ} (hF : F ∈ principalSeries ℂ n χ) {Q : Pol n}
    (hJ : HasJet σ F Q) (X : Matrix (Fin n) (Fin n) ℂ) :
    HasJet σ (holDeriv X F) (op (opDataH (alphaOf l t) X) Q) := by
  classical
  obtain ⟨N, P, hP, rfl⟩ := hJ
  have hT : ∀ m : Fin n, AdjacentGrowth.gramWeight m = evalC (gramF m) :=
    fun m => funext fun v => (evalC_gramF m v).symm
  have hTd : ∀ m : Fin n, Differentiable ℝ (AdjacentGrowth.gramWeight m) := fun m => by
    rw [hT]; exact differentiable_evalC _
  have hD : (fun x : Lw n → ℂ => ∏ m : Fin n, AdjacentGrowth.gramWeight m x) = evalC gramProdF :=
    funext fun v => (evalC_gramProdF v).symm
  set Qf : R2 n := ∑ m, C (σ m) * dW X (gramF m) * ∏ m' ∈ Finset.univ.erase m, gramF m'
  set P' : R2 n := holIncl (lamH (alphaOf l t) X) * P * gramProdF + Qf * P +
    gramProdF * dW X P - (N : R2 n) * P * dW X gramProdF
  refine ⟨N + 1, P', fun v => ?_, ?_⟩
  · have hW := wirt_weighted_apply gramWeight hTd isPosReal_gramWeight σ
      (differentiable_nbUnit_comp hF) (differentiable_evalC P) hP v (fieldW X v)
    have hQf : evalC Qf v = ∑ m, σ m * wirt (gramWeight m) v (fieldW X v) *
        ∏ m' ∈ Finset.univ.erase m, gramWeight m' v := by
      simp only [Qf, ← evalAt_apply, map_sum, map_mul, map_prod, evalAt_C]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [evalAt_apply, evalC_dW, ← hT]
      congr 1
      exact Finset.prod_congr rfl fun m' _ => by rw [evalAt_apply, evalC_gramF]
    have hP'v : evalC P' v = (∑ k, alphaOf l t k * conjMat X v k k) * evalC P v *
        (∏ m, gramWeight m v) + evalC Qf v * evalC P v +
          (∏ m, gramWeight m v) * wirt (evalC P) v (fieldW X v) -
            (N : ℂ) * evalC P v * wirt (fun x => ∏ m, gramWeight m x) v (fieldW X v) := by
      simp only [P', ← evalAt_apply, map_add, map_sub, map_mul, map_natCast]
      simp only [evalAt_apply, evalC_holIncl, eval_lamH, evalC_dW, ← hD]
    rw [holDeriv_nbUnit l t hχ hF X v, hP'v, hQf, add_mul, hW]
    have h2 := hP v
    linear_combination ((∑ k, alphaOf l t k * conjMat X v k k) * ∏ m, gramWeight m v) * h2
  · have hG : holPart (gramProdF (n := n)) = 1 := holPart_gramProdF
    have hQ0 : holPart Qf = 0 := by
      simp only [Qf, map_sum, map_mul, holPart_dW_eq_zero_of (holPart_gramF _), mul_zero,
        zero_mul, Finset.sum_const_zero]
    have hhol : holPart P' = lamH (alphaOf l t) X * holPart P +
        ∑ k, fieldWH X k * pderiv k (holPart P) := by
      simp only [P', map_add, map_sub, map_mul, map_natCast, holPart_holIncl, hG, hQ0,
        holPart_dW, holPart_dW_eq_zero_of hG]
      ring
    rw [hhol, map_add, map_mul, map_sum, op_apply, add_comm]
    simp only [opDataH, map_mul, ιP_pderiv]

end Langlands.Archimedean.HolomorphicJets
