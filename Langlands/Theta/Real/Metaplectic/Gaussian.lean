import Langlands.Theta.Real.Metaplectic.Smooth
import Langlands.Analysis.SiegelGaussianIntegral

/-!
# The Gaussian vector and the scalar of the metaplectic group

Let `φ₀ = gaussianVector l = e^{-π‖x‖²}`. For `g` in `RealMetaplecticGroup l` over
`s = [[A, B], [C, D]] ∈ Sp_{2l}(ℝ)`:

* `weilSchwartz g φ₀` is again a Gaussian: `weilSchwartz g φ₀ x = c · e^{πi xᵀ τ x}` with
  `τ = siegelPoint s = -(C - iD)(A - iB)⁻¹` in the Siegel upper half space and
  `c = gaussianScalar g = (weilSchwartz g φ₀)(0)` (`weilSchwartz_gaussianVector_apply`): the image of a
  vacuum vector of `1` is a vacuum vector of `s`, and vacuum vectors of `s` solve the first-order
  system `∂ₐ f = 2πi (τ x)ₐ f`;
* `c² · det (A - iB) = 1` (`gaussianScalar_sq_mul_det`): the normalization built into the group; so
  `g ↦ gaussianScalar g` is a square root of `det (A - iB)⁻¹`, which is where the double cover appears;
* `⟪φ₀, weil g φ₀⟫² · det(holomorphicPart s) = ⟪φ₀, φ₀⟫²` (`inner_gaussianVector_weil_sq`), with
  `holomorphicPart s = ((A + D) + i(C - B)) / 2`, by the Gaussian integral over the Siegel upper half
  space;
* for orthogonal `s` (the maximal compact `Sp ∩ O ≅ U(l)`), `τ = i`, `φ₀` is an eigenvector,
  `weil g φ₀ = c φ₀`, and `c² · det (holomorphicPart s) = 1`, `holomorphicPart s = A - iB` being the
  unitary matrix of `s` (`weilSchwartz_gaussianVector_of_orthogonal`).

Also `continuous_weilSchwartz_uncurry`: the action on Schwartz space is jointly continuous.
Lion–Vergne, *The Weil representation, Maslov index and theta series*, part I; Folland, *Harmonic
analysis in phase space*, chapter 4 (page references to be added).
-/

noncomputable section

open MeasureTheory Complex Matrix
open scoped Real SchwartzMap ComplexConjugate InnerProductSpace

namespace Langlands.Theta

open Langlands.Theta.Real.Internal

variable {l : Type} [Fintype l] [DecidableEq l]
open Langlands.Theta.Real

namespace Real

/-- The holomorphic part `((A + D) + i (C - B)) / 2` of `s = [[A, B], [C, D]]`. -/
def holomorphicPart (s : Matrix (l ⊕ l) (l ⊕ l) ℝ) : Matrix l l ℂ := fun i j =>
  ((s (.inl i) (.inl j) + s (.inr i) (.inr j) : ℝ) +
    I * (s (.inr i) (.inl j) - s (.inl i) (.inr j) : ℝ)) / 2

/-- The point `-(C - iD)(A - iB)⁻¹` of the Siegel upper half space, the image of `i · 1` under
`s = [[A, B], [C, D]]`. -/
def siegelPoint (s : Matrix (l ⊕ l) (l ⊕ l) ℝ) : Matrix l l ℂ :=
  -(automorphyLower s * (automorphyUpper s)⁻¹)

/-- `det (A - iB) ≠ 0` for symplectic `s`. -/
theorem det_automorphyUpper_ne_zero (s : Matrix.symplecticGroup l ℝ) :
    (automorphyUpper s.1).det ≠ 0 :=
  automorphyDet_ne_zero s

/-- The Siegel point of a symplectic matrix is symmetric. -/
theorem isSymm_siegelPoint (s : Matrix.symplecticGroup l ℝ) : (siegelPoint s.1).IsSymm :=
  (Matrix.det_ne_zero_and_isSymm_of_mem_symplecticGroup l s.1 _ _ (fun _ _ => rfl)
    (fun _ _ => rfl) s.2).2

/-- The Siegel point of a symplectic matrix lies in the Siegel upper half space. -/
theorem isSiegel_siegelPoint (s : Matrix.symplecticGroup l ℝ) : Matrix.IsSiegel (siegelPoint s.1) :=
  Matrix.IsSiegel.neg_mul_inv_of_symplectic l s.1 _ _ (fun _ _ => rfl) (fun _ _ => rfl) s.2
    (det_automorphyUpper_ne_zero s) (isSymm_siegelPoint s)

namespace Internal

omit [DecidableEq l] in
theorem gaussianVector_apply' (x : EuclideanSpace ℝ l) :
    gaussianVector l x = cexp (-π * ((x.ofLp ⬝ᵥ x.ofLp : ℝ) : ℂ)) := by
  rw [gaussianVector_apply]
  have e : ‖x‖ ^ 2 = x.ofLp ⬝ᵥ x.ofLp := by
    rw [EuclideanSpace.norm_sq_eq]
    simp [dotProduct, sq]
  rw [e, Complex.ofReal_exp]
  push_cast
  ring_nf

theorem gaussian_vacuum (j : l) :
    schrodingerDeriv (Pi.single (.inl j) 1) (gaussianVector l) =
      I • schrodingerDeriv (Pi.single (.inr j) 1) (gaussianVector l) := by
  have h := isVacuumFor_one_gaussianVector (l := l) j
  have e1 : ((1 : Matrix.symplecticGroup l ℝ) : Matrix (l ⊕ l) (l ⊕ l) ℝ) = 1 := rfl
  rw [e1, one_mulVec, one_mulVec] at h
  exact h

theorem schrodingerDeriv_apply_basis {l : Type} [Fintype l] [DecidableEq l] (w : l ⊕ l → ℝ) (f : RealSchwartz l)
    (x : EuclideanSpace ℝ l) :
    schrodingerDeriv w f x = ∑ b, (w (.inl b) : ℂ) * fderiv ℝ f x (EuclideanSpace.single b 1) +
      2 * π * I * (∑ b, (w (.inr b) : ℂ) * (x b : ℂ)) * f x := by
  rw [schrodingerDeriv_apply]
  have h1 : translationPart w = ∑ b, w (.inl b) • EuclideanSpace.single b (1 : ℝ) := by
    ext i
    simp [translationPart, Pi.single_apply]
  have h2 : inner ℝ (modulationPart w) x = ∑ b, w (.inr b) * x b := by
    simp [modulationPart, PiLp.inner_apply, mul_comm]
  rw [h1, map_sum, h2]
  simp [Complex.real_smul, ofReal_sum]

theorem fderiv_eq_of_annihilated : ∀ (l : Type) [Fintype l] [DecidableEq l] (s : Matrix (l ⊕ l) (l ⊕ l) ℝ)
    (P Q : Matrix l l ℂ), (∀ a b, P a b = (s (.inl a) (.inl b) : ℂ) - I * (s (.inl a) (.inr b) : ℂ)) →
    (∀ a b, Q a b = (s (.inr a) (.inl b) : ℂ) - I * (s (.inr a) (.inr b) : ℂ)) → P.det ≠ 0 →
    ∀ f : RealSchwartz l, (∀ j : l, schrodingerDeriv (s *ᵥ Pi.single (.inl j) 1) f = I • schrodingerDeriv (s *ᵥ Pi.single (.inr j) 1) f) →
    ∀ (a : l) (x : EuclideanSpace ℝ l), fderiv ℝ f x (EuclideanSpace.single a 1) =
      2 * π * I * ((-(Q * P⁻¹))ᵀ *ᵥ fun i => (x i : ℂ)) a * f x := by
  intro l _ _ s P Q hP hQ hdet f hf a x
  set u : l → ℂ := fun b => fderiv ℝ f x (EuclideanSpace.single b 1) with hu
  set xC : l → ℂ := fun i => (x i : ℂ) with hxC
  have hj : ∀ j, ∑ b, P b j * u b + 2 * π * I * (∑ b, Q b j * xC b) * f x = 0 := by
    intro j
    have e := congrArg (fun g : RealSchwartz l => g x) (hf j)
    simp only [_root_.smul_apply, smul_eq_mul, schrodingerDeriv_apply_basis] at e
    simp only [mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true] at e
    simp only [hP, hQ, sub_mul, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum]
    simp only [hu, hxC]
    linear_combination e
  have hv : Pᵀ *ᵥ u = -(2 * π * I * f x) • (Qᵀ *ᵥ xC) := by
    funext j
    simp only [mulVec, dotProduct, transpose_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination hj j
  have hunit : IsUnit Pᵀ.det := by rw [det_transpose]; exact isUnit_iff_ne_zero.mpr hdet
  have hu' : u = (Pᵀ)⁻¹ *ᵥ (Pᵀ *ᵥ u) := by rw [mulVec_mulVec, nonsing_inv_mul _ hunit, one_mulVec]
  have key : u a = ((Pᵀ)⁻¹ *ᵥ (-(2 * π * I * f x) • (Qᵀ *ᵥ xC))) a := by rw [← hv, ← hu']
  change u a = _
  rw [key, mulVec_smul, mulVec_mulVec, ← transpose_nonsing_inv, ← transpose_mul, Matrix.transpose_neg,
    Matrix.neg_mulVec]
  simp only [Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
  ring

theorem schwartz_eq_gaussian_of_fderiv_eq_mulVec :
    ∀ (l : Type) [Fintype l] [DecidableEq l] (τ : Matrix l l ℂ) (f : RealSchwartz l), τ.IsSymm →
      (∀ (a : l) (x : EuclideanSpace ℝ l),
        fderiv ℝ f x (EuclideanSpace.single a 1) = 2 * π * I * (τ *ᵥ fun i => (x i : ℂ)) a * f x) →
      ∀ x : EuclideanSpace ℝ l,
        f x = f 0 * cexp (π * I * ((fun i => (x i : ℂ)) ⬝ᵥ τ *ᵥ fun i => (x i : ℂ))) := by
  intro l _ _ τ f _hτ H x
  set v : l → ℂ := fun i => (x i : ℂ) with hv
  set c : ℂ := v ⬝ᵥ τ *ᵥ v with hc
  have hx : x = ∑ a, x a • EuclideanSpace.single a (1 : ℝ) := by
    conv_lhs => rw [← (EuclideanSpace.basisFun l ℝ).toBasis.sum_repr x]
    simp
  have hD : ∀ t : ℝ, fderiv ℝ f (t • x) x = 2 * π * I * (t * c) * f (t • x) := by
    intro t
    rw [show fderiv ℝ f (t • x) x = fderiv ℝ f (t • x) (∑ a, x a • EuclideanSpace.single a (1 : ℝ)) from
      congrArg _ hx]
    simp only [map_sum, map_smul, H, Complex.real_smul]
    have hvt : (fun i => ((t • x) i : ℂ)) = (t : ℂ) • v := by
      funext i; simp [hv]
    rw [hvt, Matrix.mulVec_smul, hc, dotProduct]
    simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul, hv]
    refine Finset.sum_congr rfl fun a _ => ?_
    ring
  set φ : ℝ → ℂ := fun t => f (t • x) * cexp (-(π * I * c) * ((t ^ 2 : ℝ) : ℂ)) with hφ
  have hφd : ∀ t : ℝ, HasDerivAt φ 0 t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => f (t • x)) (fderiv ℝ f (t • x) ((1 : ℝ) • x)) t :=
      (f.differentiableAt (x := t • x)).hasFDerivAt.comp_hasDerivAt t ((hasDerivAt_id t).smul_const x)
    have h2 : HasDerivAt (fun t : ℝ => cexp (-(π * I * c) * ((t ^ 2 : ℝ) : ℂ)))
        (cexp (-(π * I * c) * ((t ^ 2 : ℝ) : ℂ)) * (-(π * I * c) * (((2 : ℕ) * t ^ (2 - 1) : ℝ) : ℂ))) t :=
      (((hasDerivAt_pow 2 t).ofReal_comp).const_mul _).cexp
    refine (h1.mul h2).congr_deriv ?_
    rw [one_smul, hD]
    push_cast
    ring
  have hconst := is_const_of_deriv_eq_zero (fun t => (hφd t).differentiableAt) (fun t => (hφd t).deriv) 1 0
  simp only [hφ, one_smul, zero_smul, one_pow, ofReal_one, mul_one] at hconst
  norm_num at hconst
  rw [← hconst, mul_assoc, ← Complex.exp_add]
  simp

theorem holPart_eq_and_gaussian_of_orthogonal_symplectic (l : Type) [Fintype l] [DecidableEq l]
    (s : Matrix (l ⊕ l) (l ⊕ l) ℝ) (P Q : Matrix l l ℂ)
    (hP : ∀ a b, P a b = (s (.inl a) (.inl b) : ℂ) - I * (s (.inl a) (.inr b) : ℂ))
    (hQ : ∀ a b, Q a b = (s (.inr a) (.inl b) : ℂ) - I * (s (.inr a) (.inr b) : ℂ))
    (hs : s ∈ Matrix.symplecticGroup l ℝ) (ho : sᵀ * s = 1) (hd : P.det ≠ 0) :
    holomorphicPart s = P ∧ ∀ x : l → ℝ,
      cexp (π * I * ((fun i => (x i : ℂ)) ⬝ᵥ (-(Q * P⁻¹)) *ᵥ fun i => (x i : ℂ))) =
        cexp (-π * ((x ⬝ᵥ x : ℝ) : ℂ)) := by
  have hJ : s * J l ℝ = J l ℝ * s := by
    have h2 : s * J l ℝ * sᵀ = J l ℝ := SymplecticGroup.mem_iff.mp hs
    calc s * J l ℝ = s * J l ℝ * (sᵀ * s) := by rw [ho, Matrix.mul_one]
      _ = (s * J l ℝ * sᵀ) * s := by simp only [Matrix.mul_assoc]
      _ = J l ℝ * s := by rw [h2]
  have e1 : ∀ a b, s (.inl a) (.inr b) = - s (.inr a) (.inl b) := by
    intro a b
    have := congrFun (congrFun hJ (.inl a)) (.inl b)
    simpa [J, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply] using this
  have e2 : ∀ a b, s (.inr a) (.inr b) = s (.inl a) (.inl b) := by
    intro a b
    have := congrFun (congrFun hJ (.inl a)) (.inr b)
    simp [J, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply] at this
    linarith
  have hh : holomorphicPart s = P := by
    ext a b
    simp only [holomorphicPart, hP, e2, e1]
    push_cast; ring
  have hQP : Q = (-I) • P := by
    ext a b
    simp only [hP, hQ, e2, e1, Matrix.smul_apply, smul_eq_mul]
    push_cast
    ring_nf; rw [I_sq]; ring
  have hinv : -(Q * P⁻¹) = I • (1 : Matrix l l ℂ) := by
    rw [hQP, Matrix.smul_mul, mul_nonsing_inv P (isUnit_iff_ne_zero.mpr hd), neg_smul, neg_neg]
  refine ⟨hh, fun x => ?_⟩
  rw [hinv, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, smul_eq_mul]
  congr 1
  simp only [dotProduct]
  push_cast
  ring_nf; rw [I_sq]; ring

theorem vacuum_coef_sq : ∀ (l : Type) [Fintype l] [DecidableEq l] (s : Matrix (l ⊕ l) (l ⊕ l) ℝ) (P Q : Matrix l l ℂ), (∀ a b, P a b = (s (.inl a) (.inl b) : ℂ) - I * (s (.inl a) (.inr b) : ℂ)) → (∀ a b, Q a b = (s (.inr a) (.inl b) : ℂ) - I * (s (.inr a) (.inr b) : ℂ)) → P.det ≠ 0 → Matrix.IsSiegel (-(Q * P⁻¹)) → ∀ c : ℂ, c ^ 2 * P.det = 1 → (∫ x : l → ℝ, c * cexp (π * I * ((fun i => (x i : ℂ)) ⬝ᵥ (-(Q * P⁻¹)) *ᵥ fun i => (x i : ℂ))) * conj (cexp (-π * ((x ⬝ᵥ x : ℝ) : ℂ)))) ^ 2 * (holomorphicPart s).det = (∫ x : l → ℝ, cexp (-π * ((x ⬝ᵥ x : ℝ) : ℂ)) * conj (cexp (-π * ((x ⬝ᵥ x : ℝ) : ℂ)))) ^ 2 := by
  intro l _ _ s P Q hP hQ hdet hS c hc
  set K := (∫ x : l → ℝ, c * cexp (π * I * ((fun i => (x i : ℂ)) ⬝ᵥ (-(Q * P⁻¹)) *ᵥ fun i => (x i : ℂ))) * conj (cexp (-π * ((x ⬝ᵥ x : ℝ) : ℂ))))
  set J := (∫ x : l → ℝ, cexp (-π * ((x ⬝ᵥ x : ℝ) : ℂ)) * conj (cexp (-π * ((x ⬝ᵥ x : ℝ) : ℂ))))
  have h1 := siegelGaussian_pair_standardGaussian l (-(Q * P⁻¹)) c hS
  have hSI : Matrix.IsSiegel ((I • (1 : Matrix l l ℂ))) := by
    refine ⟨?_, ?_⟩
    · simp [Matrix.IsSymm]
    · have : ((I • (1 : Matrix l l ℂ)).map Complex.im) = 1 := by
        ext i j; by_cases h : i = j <;> simp [h, Matrix.one_apply]
      rw [this]; exact Matrix.PosDef.one
  have h2 := siegelGaussian_pair_standardGaussian l (I • (1 : Matrix l l ℂ)) 1 hSI
  have hJ : (∫ x : l → ℝ, (1:ℂ) * cexp (π * I * ((fun i => (x i : ℂ)) ⬝ᵥ (I • (1 : Matrix l l ℂ)) *ᵥ fun i => (x i : ℂ))) * conj (cexp (-π * ((x ⬝ᵥ x : ℝ) : ℂ)))) = J := by
    congr 1; ext x
    congr 2
    rw [one_mul]; congr 1
    rw [Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul]
    simp only [dotProduct, smul_eq_mul, Complex.ofReal_sum, Complex.ofReal_mul]
    rw [← mul_assoc, mul_assoc _ I I, I_mul_I]; ring
  rw [hJ] at h2
  have hdet2 : (1 - I • (I • (1 : Matrix l l ℂ))).det = 2 ^ Fintype.card l := by
    have : (1 - I • (I • (1 : Matrix l l ℂ))) = (2:ℂ) • (1 : Matrix l l ℂ) := by
      rw [smul_smul, I_mul_I]; ext i j; by_cases h : i = j <;> simp [h]; norm_num
    rw [this, det_smul, det_one, mul_one]
  rw [hdet2, one_pow] at h2
  have hprod : (1 - I • (-(Q * P⁻¹))) * P = (2:ℂ) • holomorphicPart s := by
    have hu : IsUnit P.det := isUnit_iff_ne_zero.mpr hdet
    rw [sub_mul, one_mul, smul_mul_assoc, neg_mul, Matrix.mul_assoc, nonsing_inv_mul _ hu, mul_one]
    ext i j
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.neg_apply, smul_eq_mul, hP, hQ, holomorphicPart]
    push_cast
    ring_nf; rw [I_sq]; ring
  have h3 : K ^ 2 * ((2:ℂ) ^ Fintype.card l * (holomorphicPart s).det) = 1 := by
    rw [← det_smul, ← hprod, det_mul, ← mul_assoc, h1, hc]
  have h2ne : (2:ℂ) ^ Fintype.card l ≠ 0 := pow_ne_zero _ two_ne_zero
  apply mul_left_cancel₀ h2ne
  linear_combination h3 - h2

end Internal

/-- The action on Schwartz space is jointly continuous in the element and the function. -/
theorem _root_.Langlands.Theta.RealMetaplecticGroup.continuous_weilSchwartz_uncurry :
    Continuous fun x : RealMetaplecticGroup l × RealSchwartz l =>
      RealMetaplecticGroup.weilSchwartz x.1 x.2 := by
  have hjoint : Continuous fun x : RealMetaplecticGroup l × RealL2 l => RealMetaplecticGroup.weil x.1 x.2 :=
    continuous_prod_of_continuous_lipschitzWith' (fun x : RealMetaplecticGroup l × RealL2 l => RealMetaplecticGroup.weil x.1 x.2) 1
      (fun g => (RealMetaplecticGroup.weil g).isometry.lipschitzWith) RealMetaplecticGroup.continuous_weil
  have hentry : ∀ a b, Continuous fun g : RealMetaplecticGroup l => (RealMetaplecticGroup.proj g : Matrix (l ⊕ l) (l ⊕ l) ℝ) a b := fun a b =>
    by
    have hv : Continuous fun g : RealMetaplecticGroup l => (RealMetaplecticGroup.proj g : Matrix (l ⊕ l) (l ⊕ l) ℝ) :=
      (continuous_subtype_val (p := fun M => M ∈ Matrix.symplecticGroup l ℝ)).comp RealMetaplecticGroup.continuous_proj
    exact (continuous_apply b).comp ((continuous_apply a).comp hv)

  have key : ∀ {A : RealSchwartz l →L[ℂ] RealSchwartz l}, A ∈ weylAlgebra l →
      Continuous fun x : RealMetaplecticGroup l × RealSchwartz l => schwartzToL2 l (A (RealMetaplecticGroup.weilSchwartz x.1 x.2)) := by
    intro A hA
    refine weylAlgebra_induction (P := fun A => Continuous fun x : RealMetaplecticGroup l × RealSchwartz l => schwartzToL2 l (A (RealMetaplecticGroup.weilSchwartz x.1 x.2)))
      ?_ ?_ ?_ ?_ ?_ hA
    · have e : (fun x : RealMetaplecticGroup l × RealSchwartz l => schwartzToL2 l ((1 : RealSchwartz l →L[ℂ] RealSchwartz l) (RealMetaplecticGroup.weilSchwartz x.1 x.2))) =
          fun x => RealMetaplecticGroup.weil x.1 (schwartzToL2 l x.2) := by
        funext x
        simp only [one_apply_eq_self, SchwartzMap.toLpCLM_apply, RealMetaplecticGroup.weil_toLp]
      rw [e]
      exact hjoint.comp (continuous_fst.prodMk ((schwartzToL2 l).continuous.comp continuous_snd))
    · intro A w ih
      simp only [toLp_dRho_omS]
      refine continuous_finsetSum _ fun a _ => ?_
      have hih : Continuous fun x : RealMetaplecticGroup l × RealSchwartz l => schwartzToL2 l (A (RealMetaplecticGroup.weilSchwartz x.1 (schrodingerDeriv (Pi.single a 1) x.2))) :=
        ih.comp (continuous_fst.prodMk ((schrodingerDeriv (Pi.single a 1)).continuous.comp continuous_snd))
      refine Continuous.smul (M := ℂ) ?_ hih
      refine continuous_ofReal.comp ?_
      simp only [mulVec, dotProduct, Matrix.neg_apply, Matrix.mul_apply, transpose_apply]
      exact continuous_finsetSum _ fun b _ => Continuous.mul (Continuous.neg (continuous_finsetSum _ fun c _ =>
        Continuous.mul (continuous_finsetSum _ fun d _ => continuous_const.mul
          ((hentry _ _).comp continuous_fst)) continuous_const)) continuous_const
    · simp only [_root_.zero_apply, map_zero]
      exact continuous_const
    · intro A B hA hB
      simp only [_root_.add_apply, map_add]
      exact hA.add hB
    · intro c A hA
      simp only [_root_.smul_apply, map_smul]
      exact hA.const_smul c
  rw [continuous_iff_continuousAt]
  intro x0
  unfold ContinuousAt
  rw [(schwartz_withSeminorms ℂ (EuclideanSpace ℝ l) ℂ).tendsto_nhds]
  rintro ⟨k, n⟩ ε hε
  obtain ⟨A, hA, hb⟩ := exists_seminorm_le_sum_norm_toLp (l := l) k n
  have ht : Filter.Tendsto (fun x : RealMetaplecticGroup l × RealSchwartz l => ∑ r, ‖schwartzToL2 l (A r (RealMetaplecticGroup.weilSchwartz x.1 x.2)) - schwartzToL2 l (A r (RealMetaplecticGroup.weilSchwartz x0.1 x0.2))‖)
      (nhds x0) (nhds 0) := by
    have : (0 : ℝ) = ∑ r : Fin n → l, ‖schwartzToL2 l (A r (RealMetaplecticGroup.weilSchwartz x0.1 x0.2)) - schwartzToL2 l (A r (RealMetaplecticGroup.weilSchwartz x0.1 x0.2))‖ := by simp
    rw [this]
    exact tendsto_finsetSum _ fun r _ => ((((key (hA r)).sub continuous_const).norm).tendsto x0)
  filter_upwards [ht.eventually (gt_mem_nhds hε)] with x hx
  refine lt_of_le_of_lt ?_ hx
  rw [SchwartzMap.schwartzSeminormFamily_apply]
  refine (hb _).trans (le_of_eq ?_)
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [← SchwartzMap.toLpCLM_apply (𝕜 := ℂ), map_sub, map_sub]

end Real

namespace RealMetaplecticGroup

/-- The value at `0` of the transformed Gaussian: `(weilSchwartz g φ₀)(0)`. -/
def gaussianScalar (g : RealMetaplecticGroup l) : ℂ := weilSchwartz g (gaussianVector l) 0

/-- The normalization: `gaussianScalar g ² · det (A - iB) = 1`. -/
theorem gaussianScalar_sq_mul_det (g : RealMetaplecticGroup l) :
    gaussianScalar g ^ 2 * (automorphyUpper (proj g).1).det = 1 := by
  have h := isNormalizedLift_weilSchwartz g 1 (gaussianVector l) isVacuumFor_one_gaussianVector
  have e1 : ((1 : Matrix.symplecticGroup l ℝ) : Matrix (l ⊕ l) (l ⊕ l) ℝ) = 1 := rfl
  rw [e1, Matrix.mul_one, gaussianVector_zero, automorphyDet_one, one_pow, one_mul] at h
  exact h

/-- The transformed Gaussian is the Gaussian of the Siegel point:
`weilSchwartz g φ₀ x = gaussianScalar g · e^{πi xᵀ τ x}`, `τ = siegelPoint (proj g)`. -/
theorem weilSchwartz_gaussianVector_apply (g : RealMetaplecticGroup l) (x : EuclideanSpace ℝ l) :
    weilSchwartz g (gaussianVector l) x = gaussianScalar g *
      cexp (π * I * ((fun i => (x i : ℂ)) ⬝ᵥ siegelPoint (proj g).1 *ᵥ fun i => (x i : ℂ))) := by
  obtain ⟨hdet, hS⟩ := Matrix.det_ne_zero_and_isSymm_of_mem_symplecticGroup l (proj g).1 _ _
    (fun _ _ => rfl) (fun _ _ => rfl) (proj g).2
  have hann : ∀ j : l, schrodingerDeriv ((proj g).1 *ᵥ Pi.single (.inl j) 1)
      (weilSchwartz g (gaussianVector l)) =
      I • schrodingerDeriv ((proj g).1 *ᵥ Pi.single (.inr j) 1) (weilSchwartz g (gaussianVector l)) :=
    fun j => by
      rw [← weilSchwartz_schrodingerDeriv, ← weilSchwartz_schrodingerDeriv, gaussian_vacuum j, map_smul]
  have hd := fderiv_eq_of_annihilated l (proj g).1 _ _ (fun _ _ => rfl) (fun _ _ => rfl) hdet
    (weilSchwartz g (gaussianVector l)) hann
  rw [hS.eq] at hd
  exact schwartz_eq_gaussian_of_fderiv_eq_mulVec l _ (weilSchwartz g (gaussianVector l)) hS hd x

/-- The vacuum matrix coefficient: `⟪φ₀, weil g φ₀⟫² · det (holomorphicPart s) = ⟪φ₀, φ₀⟫²`. -/
theorem inner_gaussianVector_weil_sq (g : RealMetaplecticGroup l) :
    ⟪(gaussianVector l).toLp 2, weil g ((gaussianVector l).toLp 2)⟫_ℂ ^ 2 *
        (holomorphicPart (proj g).1).det =
      ⟪(gaussianVector l).toLp 2, (gaussianVector l).toLp 2⟫_ℂ ^ 2 := by
  have key := vacuum_coef_sq l (proj g).1 _ _ (fun _ _ => rfl) (fun _ _ => rfl)
    (det_automorphyUpper_ne_zero (proj g)) (isSiegel_siegelPoint (proj g)) (gaussianScalar g)
    (gaussianScalar_sq_mul_det g)
  have hmp := EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp l
  have hint : ∀ f h : RealSchwartz l, ⟪f.toLp 2, h.toLp 2⟫_ℂ =
      ∫ x : l → ℝ, h (WithLp.toLp 2 x) * conj (f (WithLp.toLp 2 x)) := by
    intro f h
    rw [SchwartzMap.inner_toL2_toL2_eq f h volume, ← hmp.symm.integral_comp']
    refine integral_congr_ae (.of_forall fun x => ?_)
    simp [mul_comm]
  rw [weil_toLp, hint, hint]
  simp only [weilSchwartz_gaussianVector_apply, gaussianVector_apply']
  exact key

/-- On the maximal compact subgroup (orthogonal `s`) the Gaussian is an eigenvector, and
`gaussianScalar g ² · det (holomorphicPart s) = 1`. -/
theorem weilSchwartz_gaussianVector_of_orthogonal (g : RealMetaplecticGroup l)
    (h : (proj g).1ᵀ * (proj g).1 = 1) :
    weilSchwartz g (gaussianVector l) = gaussianScalar g • gaussianVector l ∧
      gaussianScalar g ^ 2 * (holomorphicPart (proj g).1).det = 1 := by
  obtain ⟨hP, hq⟩ := holPart_eq_and_gaussian_of_orthogonal_symplectic l (proj g).1 _ _
    (fun _ _ => rfl) (fun _ _ => rfl) (proj g).2 h (det_automorphyUpper_ne_zero (proj g))
  refine ⟨?_, by rw [hP]; exact gaussianScalar_sq_mul_det g⟩
  ext x
  rw [weilSchwartz_gaussianVector_apply, _root_.smul_apply, smul_eq_mul, gaussianVector_apply']
  exact congrArg (gaussianScalar g * ·) (hq x.ofLp)

end RealMetaplecticGroup

end Langlands.Theta
