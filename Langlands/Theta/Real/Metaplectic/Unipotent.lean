import Langlands.Theta.Real.Metaplectic.Basic

/-!
# The metaplectic group over unipotent elements (internal)

* `automorphyDet_ne_zero`: for `s = [[A, B], [C, D]]` symplectic, `det (A - iB) ≠ 0` (the rows of
  `A - iB` and of `C - iD` combine to the identity through the symplectic relations).
* For a symmetric `S`, the unipotent symplectic matrices `nn S t` and the operators
  `UU S t = 𝓕 ∘ chirp (-t S) ∘ 𝓕⁻¹` that lift them, and the normalization of these operators on
  vacuum vectors (`isNormalizedLift_unipotent`), obtained by differentiating in `t` the identity
  between `(UU S t f)(0)² det(...)` and `f(0)² det(...)`.

Used for the section over the big cell (`Theta/Real/Metaplectic/BigCell`).
-/

noncomputable section

open MeasureTheory Complex SchwartzMap Matrix Filter Topology FourierTransform LineDeriv
open scoped Real ContDiff RealInnerProductSpace

namespace Langlands.Theta

open Langlands.Theta.Real.Internal

variable {l : Type} [Fintype l] [DecidableEq l]

namespace Real

namespace Internal

theorem J_mul_transpose_inl (s : Matrix (l ⊕ l) (l ⊕ l) ℝ) (a : l) (j : l ⊕ l) :
    (Matrix.J l ℝ * sᵀ) (.inl a) j = -s j (.inr a) := by
  simp [Matrix.J, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]

theorem J_mul_transpose_inr (s : Matrix (l ⊕ l) (l ⊕ l) ℝ) (a : l) (j : l ⊕ l) :
    (Matrix.J l ℝ * sᵀ) (.inr a) j = s j (.inl a) := by
  simp [Matrix.J, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]

theorem sp_rel (s : Matrix.symplecticGroup l ℝ) (i j : l ⊕ l) :
    ∑ a, (s.1 i (.inr a) * s.1 j (.inl a) - s.1 i (.inl a) * s.1 j (.inr a)) = Matrix.J l ℝ i j := by
  have h := congrFun (congrFun (SymplecticGroup.mem_iff.1 s.2) i) j
  rw [Matrix.mul_assoc, Matrix.mul_apply, Fintype.sum_sum_type] at h
  simp only [J_mul_transpose_inl, J_mul_transpose_inr] at h
  rw [← h, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun a _ => by ring

end Internal

/-- The automorphy determinant `det (A - iB)` of a symplectic matrix does not vanish. -/
theorem automorphyDet_ne_zero (s : Matrix.symplecticGroup l ℝ) : automorphyDet s.1 ≠ 0 := by
  let N : Matrix l (l ⊕ l) ℝ := Matrix.of fun a k => s.1 (.inl a) k
  let K : Matrix (l ⊕ l) l ℝ := Matrix.of fun k b =>
    Sum.elim (fun c => s.1 (.inr b) (.inr c)) (fun c => -s.1 (.inr b) (.inl c)) k
  have hNK : N * K = 1 := by
    ext a b
    have h := sp_rel s (.inl a) (.inr b)
    rw [Matrix.mul_apply, Fintype.sum_sum_type]
    simp only [N, K, Matrix.of_apply, Sum.elim_inl, Sum.elim_inr]
    calc _ = -∑ c, (s.1 (.inl a) (.inr c) * s.1 (.inr b) (.inl c) - s.1 (.inl a) (.inl c) * s.1 (.inr b) (.inr c)) := by
          rw [← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
          exact Finset.sum_congr rfl fun c _ => by ring
      _ = _ := by rw [h]; simp [Matrix.J, Matrix.one_apply]
  have hM : (N * Nᵀ).det ≠ 0 := by
    intro hd
    obtain ⟨v, hv, hvM⟩ := Matrix.exists_vecMul_eq_zero_iff.2 hd
    have h1 : (v ᵥ* N) ⬝ᵥ (v ᵥ* N) = 0 := by
      have : (v ᵥ* (N * Nᵀ)) ⬝ᵥ v = 0 := by rw [hvM, zero_dotProduct]
      rwa [← Matrix.vecMul_vecMul, ← Matrix.dotProduct_mulVec, Matrix.mulVec_transpose] at this
    have h2 : v ᵥ* N = 0 := dotProduct_self_eq_zero.1 h1
    apply hv
    calc v = v ᵥ* (N * K) := by rw [hNK, Matrix.vecMul_one]
      _ = 0 := by rw [← Matrix.vecMul_vecMul, h2, Matrix.zero_vecMul]
  let W : Matrix l l ℂ := Matrix.of fun c b => (s.1 (.inl b) (.inl c) : ℂ) + I * s.1 (.inl b) (.inr c)
  have hPW : automorphyUpper s.1 * W = (N * Nᵀ).map ofReal := by
    ext a b
    have hs := sp_rel s (.inl a) (.inl b)
    simp only [Matrix.J, fromBlocks_apply₁₁, Matrix.zero_apply] at hs
    have e : ∀ c, ((s.1 (.inl a) (.inl c) : ℂ) - I * s.1 (.inl a) (.inr c)) *
        ((s.1 (.inl b) (.inl c) : ℂ) + I * s.1 (.inl b) (.inr c)) =
        ((s.1 (.inl a) (.inl c) * s.1 (.inl b) (.inl c) + s.1 (.inl a) (.inr c) * s.1 (.inl b) (.inr c) : ℝ) : ℂ) -
        I * ((s.1 (.inl a) (.inr c) * s.1 (.inl b) (.inl c) - s.1 (.inl a) (.inl c) * s.1 (.inl b) (.inr c) : ℝ) : ℂ) :=
      fun c => by
        push_cast
        linear_combination (-((s.1 (.inl a) (.inr c) : ℂ) * (s.1 (.inl b) (.inr c) : ℂ))) * I_sq
    simp only [Matrix.mul_apply, automorphyUpper, W, Matrix.of_apply, Matrix.map_apply, N, Matrix.transpose_apply,
      Fintype.sum_sum_type]
    rw [Finset.sum_congr rfl fun c _ => e c, Finset.sum_sub_distrib, ← Finset.mul_sum, ← ofReal_sum, ← ofReal_sum, hs]
    push_cast
    rw [Finset.sum_add_distrib]
    simp
  have e : ((N * Nᵀ).map ofReal).det = ((N * Nᵀ).det : ℂ) := by
    rw [show (N * Nᵀ).map ofReal = ofRealHom.mapMatrix (N * Nᵀ) from rfl, ← RingHom.map_det]
    rfl
  intro h0
  have := congrArg Matrix.det hPW
  rw [Matrix.det_mul, e] at this
  unfold automorphyDet at h0
  rw [h0, zero_mul] at this
  exact hM (ofReal_eq_zero.1 this.symm)

namespace Internal

def nn (S : Matrix l l ℝ) (t : ℝ) : Matrix (l ⊕ l) (l ⊕ l) ℝ := fromBlocks 1 (t • S) 0 1

theorem nn_mem {S : Matrix l l ℝ} (hS : S.IsSymm) (t : ℝ) : nn S t ∈ Matrix.symplecticGroup l ℝ := by
  rw [SymplecticGroup.mem_iff, nn, Matrix.J, fromBlocks_transpose, fromBlocks_multiply, fromBlocks_multiply]
  simp [hS.eq]

theorem upperPart_unipotent_mul (S : Matrix l l ℝ) (t : ℝ) (s : Matrix (l ⊕ l) (l ⊕ l) ℝ) :
    automorphyUpper (nn S t * s) = automorphyUpper s + (t : ℂ) • (S.map ofReal * automorphyLower s) := by
  ext a b
  simp only [automorphyUpper, automorphyLower, nn, Matrix.add_apply, Matrix.mul_apply, Fintype.sum_sum_type, fromBlocks_apply₁₁,
    fromBlocks_apply₁₂, Matrix.one_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, ite_mul, one_mul,
    zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true, ofReal_add, ofReal_sum, ofReal_mul]
  have e : ∀ u v : l → ℝ, ∑ c, (t : ℂ) * (S a c : ℂ) * (u c : ℂ) - I * ∑ c, (t : ℂ) * (S a c : ℂ) * (v c : ℂ) =
      (t : ℂ) * ∑ c, (S a c : ℂ) * ((u c : ℂ) - I * (v c : ℂ)) := fun u v => by
    simp only [Finset.mul_sum]
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun c _ => by ring
  rw [← e]
  ring

theorem loQ_nn (S : Matrix l l ℝ) (t : ℝ) (s : Matrix (l ⊕ l) (l ⊕ l) ℝ) : automorphyLower (nn S t * s) = automorphyLower s := by
  ext a b
  simp [automorphyLower, nn, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]

theorem tc_apply (M : Matrix l l ℝ) (x : EuclideanSpace ℝ l) (a : l) :
    Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) M x a = ∑ b, M a b * x b := rfl

theorem metaplectic_unipotent_block_first_diag (S : Matrix l l ℝ) (t : ℝ) : blockCLM Sum.inl Sum.inl (nn S t) = 1 := by
  ext x a
  simp [blockCLM_apply, nn, Matrix.one_apply]

theorem metaplectic_unipotent_block_upper (S : Matrix l l ℝ) (t : ℝ) :
    blockCLM Sum.inl Sum.inr (nn S t) = t • Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) S := by
  ext x a
  simp [blockCLM_apply, nn, tc_apply, Finset.mul_sum, mul_assoc]

theorem metaplectic_unipotent_block_lower (S : Matrix l l ℝ) (t : ℝ) : blockCLM Sum.inr Sum.inl (nn S t) = 0 := by
  ext x a
  simp [blockCLM_apply, nn]

theorem metaplectic_unipotent_block_second_diag (S : Matrix l l ℝ) (t : ℝ) : blockCLM Sum.inr Sum.inr (nn S t) = 1 := by
  ext x a
  simp [blockCLM_apply, nn, Matrix.one_apply]

def UU (S : Matrix l l ℝ) (t : ℝ) : RealSchwartz l →L[ℂ] RealSchwartz l :=
  fourierCLM ℂ (RealSchwartz l) * (chirp (-(t • Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) S)) * fourierInvCLM ℂ (RealSchwartz l))

theorem inner_sym {S : Matrix l l ℝ} (hS : S.IsSymm) (t : ℝ) (x y : EuclideanSpace ℝ l) :
    ⟪x, (-(t • Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) S)) y⟫ =
      ⟪y, (-(t • Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) S)) x⟫ := by
  have hS' : ∀ a b, S a b = S b a := fun a b => by
    simpa using (congrFun (congrFun hS.eq b) a)
  simp only [_root_.neg_apply, _root_.smul_apply, inner_neg_right, real_inner_smul_right]
  congr 2
  simp only [PiLp.inner_apply, tc_apply, RCLike.inner_apply, conj_trivial, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [hS']
  ring

theorem intw_UU {S : Matrix l l ℝ} (hS : S.IsSymm) (t : ℝ) (p q : EuclideanSpace ℝ l) :
    IntertwinesAt (UU S t) p q (p + (t • Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) S) q) q := by
  have h := (intertwinesAt_fourierCLM _ _).mul ((intertwinesAt_chirp (inner_sym hS t) _ _).mul (intertwinesAt_fourierInvCLM p q))
  rw [show p + (t • Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) S) q =
    -(-p + (-(t • Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) S)) q) by
      rw [_root_.neg_apply, neg_add, neg_neg, neg_neg]]
  exact h

theorem impl_UU {S : Matrix l l ℝ} (hS : S.IsSymm) (t : ℝ) :
    Intertwines (fun w => nn S t *ᵥ w) (UU S t).toLinearMap :=
  Intertwines.of_rhoFun
    (fun f => (isL2Isometry_fourierCLM.mul ((isL2Isometry_chirp _).mul isL2Isometry_fourierInvCLM)) f)
    fun w f g hg => by
    have := intw_UU hS t (translationPart w) (modulationPart w) f g hg
    rw [rhoFun_eq, translationPart_mulVec, modulationPart_mulVec, metaplectic_unipotent_block_first_diag,
      metaplectic_unipotent_block_upper, metaplectic_unipotent_block_lower, metaplectic_unipotent_block_second_diag]
    simpa using this

theorem isUnit_UU (S : Matrix l l ℝ) (t : ℝ) : IsUnit (UU S t) :=
  isUnit_fourierCLM.mul ((isUnit_chirp _).mul isUnit_fourierInvCLM)

theorem UU_dRho {S : Matrix l l ℝ} (hS : S.IsSymm) (t : ℝ) (w : l ⊕ l → ℝ) (f : RealSchwartz l) :
    UU S t (schrodingerDeriv w f) = schrodingerDeriv (nn S t *ᵥ w) (UU S t f) := by
  have hs : Function.Surjective (UU S t).toLinearMap := fun f => ⟨Ring.inverse (UU S t) f, by
    show (UU S t * Ring.inverse (UU S t)) f = f
    rw [Ring.mul_inverse_cancel _ (isUnit_UU S t), one_apply_eq_self]⟩
  exact Intertwines.comm_schrodingerDeriv (s := Matrix.mulVecLin (nn S t)) (impl_UU hS t) hs w f

theorem UU_zero (S : Matrix l l ℝ) : UU S 0 = 1 := by
  have h0 : (0 : ℝ) • Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) S = 0 := by ext x; simp
  simp [UU, h0, chirp_zero, fourierCLM_mul_fourierInvCLM]

omit [DecidableEq l] in
theorem fourierCLM_apply_zero (h : RealSchwartz l) : fourierCLM ℂ (RealSchwartz l) h 0 = ∫ x, h x := by
  rw [FourierTransform.fourierCLM_apply, fourier_coe, Real.fourier_eq]
  simp

theorem hasDerivAt_UU (S : Matrix l l ℝ) (f : RealSchwartz l) (t₀ : ℝ) :
    HasDerivAt (fun t => UU S t f 0)
      (fourierCLM ℂ (RealSchwartz l) (quadMul (-(Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) S)) (fourierInvCLM ℂ (RealSchwartz l) (UU S t₀ f))) 0) t₀ := by
  have e1 : ∀ t, UU S t f 0 = ∫ x, chirp (-(t • Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) S)) (fourierInvCLM ℂ (RealSchwartz l) f) x := fun t => by
    rw [UU, mul_apply_eq_comp, mul_apply_eq_comp, fourierCLM_apply_zero]
  have e2 : fourierInvCLM ℂ (RealSchwartz l) (UU S t₀ f) = chirp (-(t₀ • Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) S)) (fourierInvCLM ℂ (RealSchwartz l) f) := by
    rw [UU, ← mul_apply_eq_comp, ← mul_assoc, fourierInvCLM_mul_fourierCLM, one_mul, mul_apply_eq_comp]
  have hq : ∀ x : EuclideanSpace ℝ l, |⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) S x⟫| ≤
      ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) S‖ * ‖x‖ ^ 2 := fun x =>
    (abs_real_inner_le_norm _ _).trans (by
      calc ‖x‖ * ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) S x‖
          ≤ ‖x‖ * (‖Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) S‖ * ‖x‖) := by
            gcongr
            exact (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) S).le_opNorm x
        _ = _ := by ring)
  have ph_eq : ∀ (t : ℝ) (x : EuclideanSpace ℝ l), chirp (-(t • Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) S)) (fourierInvCLM ℂ (RealSchwartz l) f) x =
      exp (((π * ⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) S x⟫ * t : ℝ) : ℂ) * I) * fourierInvCLM ℂ (RealSchwartz l) f x := fun t x => by
    have : -π * ⟪x, (-(t • Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) S)) x⟫ =
        π * ⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) S x⟫ * t := by
      simp only [_root_.neg_apply, _root_.smul_apply, inner_neg_right,
        real_inner_smul_right]
      ring
    rw [chirp_apply, this]
  have mq_eq : ∀ (h : RealSchwartz l) (x : EuclideanSpace ℝ l), quadMul (-(Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) S)) h x =
      ((π * ⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) S x⟫ : ℝ) : ℂ) * I * h x := fun h x => by
    have : -π * ⟪x, (-(Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) S)) x⟫ =
        π * ⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) S x⟫ := by
      simp only [_root_.neg_apply, inner_neg_right]
      ring
    rw [quadMul_apply, this]
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (x₀ := t₀)
    (F := fun t x => chirp (-(t • Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) S)) (fourierInvCLM ℂ (RealSchwartz l) f) x)
    (F' := fun t x => quadMul (-(Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) S))
      (chirp (-(t • Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) S)) (fourierInvCLM ℂ (RealSchwartz l) f)) x)
    (bound := fun x => π * ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) S‖ * (‖x‖ ^ 2 * ‖fourierInvCLM ℂ (RealSchwartz l) f x‖))
    Filter.univ_mem (.of_forall fun t => (chirp _ (fourierInvCLM ℂ (RealSchwartz l) f)).continuous.aestronglyMeasurable)
    ((chirp _ (fourierInvCLM ℂ (RealSchwartz l) f)).integrable) ((quadMul _ _).continuous.aestronglyMeasurable)
    (.of_forall fun x t _ => by
      rw [mq_eq, ph_eq, norm_mul, norm_mul, norm_mul, norm_I, norm_exp_ofReal_mul_I, Complex.norm_real,
        Real.norm_eq_abs, abs_mul, abs_of_pos Real.pi_pos]
      have h1 := hq x
      have h2 := norm_nonneg (fourierInvCLM ℂ (RealSchwartz l) f x)
      calc π * |⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) S x⟫| * 1 * (1 * ‖fourierInvCLM ℂ (RealSchwartz l) f x‖)
          = π * (|⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) S x⟫| * ‖fourierInvCLM ℂ (RealSchwartz l) f x‖) := by ring
        _ ≤ π * ((‖Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) S‖ * ‖x‖ ^ 2) * ‖fourierInvCLM ℂ (RealSchwartz l) f x‖) := by gcongr
        _ = _ := by ring)
    (((fourierInvCLM ℂ (RealSchwartz l) f).integrable_pow_mul volume 2).const_mul _)
    (.of_forall fun x t _ => by
      simp only [ph_eq, mq_eq]
      have h1 : HasDerivAt (fun t : ℝ => ((π * ⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) S x⟫ * t : ℝ) : ℂ))
          ((π * ⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) S x⟫ : ℝ) : ℂ) t := by
        have := ((hasDerivAt_id t).const_mul (π * ⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) S x⟫)).ofReal_comp
        simpa using this
      exact ((h1.mul_const I).cexp.mul_const (fourierInvCLM ℂ (RealSchwartz l) f x)).congr_deriv (by ring))
  rw [e2, fourierCLM_apply_zero]
  exact key.2.congr_of_eventuallyEq (.of_forall e1)

theorem dRho_eval_zero (w : l ⊕ l → ℝ) (h : RealSchwartz l) :
    schrodingerDeriv w h 0 = ∑ a, (w (.inl a) : ℂ) * (∂_{(EuclideanSpace.single a 1 : EuclideanSpace ℝ l)} h) 0 := by
  rw [schrodingerDeriv_eq_sum w]
  simp [Fintype.sum_sum_type, schrodingerDeriv_single_inl, schrodingerDeriv_single_inr]

theorem hess {s : Matrix (l ⊕ l) (l ⊕ l) ℝ} {H : RealSchwartz l} (hA : IsVacuumFor s H) (j k : l) :
    ∑ a, automorphyUpper s a j * (∂_{(EuclideanSpace.single a 1 : EuclideanSpace ℝ l)} (∂_{(EuclideanSpace.single k 1 : EuclideanSpace ℝ l)} H)) 0 =
      -(2 * π * I) * automorphyLower s k j * H 0 := by
  have comm : ∀ w, schrodingerDeriv (Pi.single (.inl k) 1) (schrodingerDeriv w H) =
      schrodingerDeriv w (∂_{(EuclideanSpace.single k 1 : EuclideanSpace ℝ l)} H) + (2 * π * I * sympl (Pi.single (.inl k) 1) w : ℂ) • H :=
    fun w => by
      have := congrArg (fun T : RealSchwartz l →L[ℂ] RealSchwartz l => T H) (schrodingerDeriv_comm_sympl (Pi.single (.inl k) 1) w)
      simp only [_root_.sub_apply, mul_apply_eq_comp, _root_.smul_apply,
        one_apply_eq_self] at this
      rw [← schrodingerDeriv_single_inl, ← this]
      abel
  have hsy : ∀ w : l ⊕ l → ℝ, sympl (Pi.single (.inl k) 1) w = w (.inr k) := fun w => by
    simp [sympl, translationPart, modulationPart, PiLp.inner_apply, Pi.single_apply]
  have hcol : ∀ b c, (s *ᵥ Pi.single b 1) c = s c b := fun b c => by
    simp [mulVec, dotProduct, Pi.single_apply]
  have e := congrArg (fun u : RealSchwartz l => schrodingerDeriv (Pi.single (.inl k) 1) u 0) (hA j)
  simp only [map_smul, _root_.smul_apply, smul_eq_mul, comm, _root_.add_apply, dRho_eval_zero, hsy,
    hcol] at e
  simp only [automorphyUpper, automorphyLower, sub_mul, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum]
  linear_combination e

theorem trace_eq {P Q : Matrix l l ℂ} (hP : P.det ≠ 0) (S M : Matrix l l ℂ) (c : ℂ)
    (h : ∀ j k, ∑ a, P a j * M a k = c * Q k j) : ∑ j, ∑ k, S j k * M j k = c * (P⁻¹ * (S * Q)).trace := by
  have h1 : Pᵀ * M = c • Qᵀ := by
    ext j k
    simp [Matrix.mul_apply, h]
  have hu : IsUnit Pᵀ.det := by
    rw [det_transpose]
    exact hP.isUnit
  have h2 : M = Pᵀ⁻¹ * (c • Qᵀ) := by
    rw [← h1, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul]
  have h3 : ∑ j, ∑ k, S j k * M j k = (S * Mᵀ).trace := by
    simp [Matrix.trace, Matrix.mul_apply]
  have h4 : S * (Pᵀ⁻¹ * (c • Qᵀ))ᵀ = c • (S * Q * P⁻¹) := by
    rw [transpose_mul, transpose_smul, transpose_transpose, transpose_nonsing_inv, transpose_transpose,
      Matrix.smul_mul, Matrix.mul_smul, ← Matrix.mul_assoc]
  rw [h3, h2, h4, trace_smul, smul_eq_mul, Matrix.trace_mul_comm]

theorem hasDerivAt_det (P K : Matrix l l ℂ) (t₀ : ℝ) (hP : (P + (t₀ : ℂ) • K).det ≠ 0) :
    HasDerivAt (fun t : ℝ => (P + (t : ℂ) • K).det)
      ((P + (t₀ : ℂ) • K).det * ((P + (t₀ : ℂ) • K)⁻¹ * K).trace) t₀ := by
  have hu : IsUnit (P + (t₀ : ℂ) • K).det := hP.isUnit
  have e : ∀ t : ℝ, (P + (t : ℂ) • K).det = (P + (t₀ : ℂ) • K).det *
      (1 + ((P + (t₀ : ℂ) • K)⁻¹ * K).trace * ((t - t₀ : ℝ) : ℂ) +
        (det (1 + (Polynomial.X : Polynomial ℂ) • ((P + (t₀ : ℂ) • K)⁻¹ * K).map Polynomial.C)).divX.divX.eval
          ((t - t₀ : ℝ) : ℂ) * ((t - t₀ : ℝ) : ℂ) ^ 2) := fun t => by
    rw [← Matrix.det_one_add_smul, ← Matrix.det_mul, Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul,
      ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.one_mul, ofReal_sub, sub_smul]
    congr 1
    abel
  have hφ : HasDerivAt (fun z : ℂ => 1 + ((P + (t₀ : ℂ) • K)⁻¹ * K).trace * z +
      (det (1 + (Polynomial.X : Polynomial ℂ) • ((P + (t₀ : ℂ) • K)⁻¹ * K).map Polynomial.C)).divX.divX.eval z * z ^ 2)
      ((P + (t₀ : ℂ) • K)⁻¹ * K).trace ((t₀ - t₀ : ℝ) : ℂ) := by
    have := (((hasDerivAt_id (0 : ℂ)).const_mul ((P + (t₀ : ℂ) • K)⁻¹ * K).trace).const_add 1).add
      ((Polynomial.hasDerivAt (det (1 + (Polynomial.X : Polynomial ℂ) •
        ((P + (t₀ : ℂ) • K)⁻¹ * K).map Polynomial.C)).divX.divX (0 : ℂ)).mul ((hasDerivAt_id (0 : ℂ)).pow 2))
    rw [sub_self, ofReal_zero]
    exact (this.congr_deriv (by simp)).congr_of_eventuallyEq (.of_forall fun z => by simp)
  have hh : HasDerivAt (fun t : ℝ => ((t - t₀ : ℝ) : ℂ)) 1 t₀ := by
    simpa using ((hasDerivAt_id t₀).sub_const t₀).ofReal_comp
  have := (hφ.comp t₀ hh).const_mul (P + (t₀ : ℂ) • K).det
  rw [mul_one] at this
  exact this.congr_of_eventuallyEq (.of_forall e)

/-- The normalization of the unipotent operators over `[[1, 0], [t S, 1]]`-type elements, in the
form used for the big cell: the operator `𝓕 ∘ chirp (-S) ∘ 𝓕⁻¹` satisfies the vacuum normalization
over `nn S 1`. -/
theorem isNormalizedLift_unipotent (S : Matrix l l ℝ) (hS : S.IsSymm) (s' : Matrix.symplecticGroup l ℝ)
    (f : RealSchwartz l) (hf : IsVacuumFor s'.1 f) :
    (fourierCLM ℂ (RealSchwartz l) (chirp (-(Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) S))
      (fourierInvCLM ℂ (RealSchwartz l) f)) 0) ^ 2 *
        (automorphyUpper s'.1 + S.map Complex.ofReal * automorphyLower s'.1).det =
      (f 0) ^ 2 * automorphyDet s'.1 := by
  have hPt : ∀ t : ℝ, automorphyUpper (nn S t * s'.1) = automorphyUpper s'.1 + (t : ℂ) • (S.map ofReal * automorphyLower s'.1) := fun t => upperPart_unipotent_mul S t s'.1
  have hdet : ∀ t : ℝ, (automorphyUpper s'.1 + (t : ℂ) • (S.map ofReal * automorphyLower s'.1)).det ≠ 0 := fun t => by
    rw [← hPt]
    exact automorphyDet_ne_zero ⟨_, mul_mem (nn_mem hS t) s'.2⟩
  have hAnn : ∀ t, IsVacuumFor (nn S t * s'.1) (UU S t f) := fun t => hf.map (UU_dRho hS t)
  have hF : ∀ t : ℝ, HasDerivAt (fun t => UU S t f 0) (-(1 / 2 : ℂ) * UU S t f 0 *
      ((automorphyUpper s'.1 + (t : ℂ) • (S.map ofReal * automorphyLower s'.1))⁻¹ * (S.map ofReal * automorphyLower s'.1)).trace) t := fun t => by
    have h1 := hasDerivAt_UU S f t
    rw [fourierCLM_quadMul_fourierInvCLM] at h1
    simp only [_root_.smul_apply, _root_.sum_apply, smul_eq_mul] at h1
    have h2 := trace_eq (hdet t) (S.map ofReal)
      (Matrix.of fun a k => (∂_{(EuclideanSpace.single a 1 : EuclideanSpace ℝ l)} (∂_{(EuclideanSpace.single k 1 : EuclideanSpace ℝ l)}
        (UU S t f))) 0) (-(2 * π * I) * UU S t f 0) (fun j k => by
          have := hess (hAnn t) j k
          rw [hPt, loQ_nn] at this
          simp only [Matrix.of_apply]
          rw [this]
          ring)
    simp only [Matrix.of_apply, Matrix.map_apply] at h2
    rw [h2] at h1
    convert h1 using 1
    have hπ : (π : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
    have hI : (I : ℂ) ≠ 0 := I_ne_zero
    field_simp
    ring
  have hh : ∀ t : ℝ, HasDerivAt (fun t => UU S t f 0 * UU S t f 0 *
      (automorphyUpper s'.1 + (t : ℂ) • (S.map ofReal * automorphyLower s'.1)).det) 0 t := fun t => by
    exact (((hF t).fun_mul (hF t)).fun_mul (hasDerivAt_det _ _ t (hdet t))).congr_deriv (by ring)
  have hc := is_const_of_deriv_eq_zero (fun t => (hh t).differentiableAt) (fun t => (hh t).deriv) 1 0
  have e0 : UU S 0 f = f := by rw [UU_zero]; rfl
  have e1 : UU S 1 f = fourierCLM ℂ (RealSchwartz l) (chirp (-(Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) S)) (fourierInvCLM ℂ (RealSchwartz l) f)) := by
    simp [UU]
  simp only [e0, e1, ofReal_zero, ofReal_one, zero_smul, add_zero, one_smul] at hc
  rw [sq, sq]
  exact hc

end Internal

end Real

end Langlands.Theta
