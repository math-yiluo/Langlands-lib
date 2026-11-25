import Langlands.Theta.Real.Metaplectic.Unipotent

/-!
# The metaplectic group over the big cell

* `RealMetaplecticGroup.exists_weilSchwartz_eq_smul_bigCellSection`: for `s ∈ Sp_{2l}(ℝ)` with
  `det A ≠ 0`, some `z • bigCellSection s` with `|z| = 1` is an `L²`-isometric normalized
  intertwiner over `s`, hence the operator of an element over `s`; `z = 1` when `det A > 0`. The
  normalization is reduced to the unipotent case by `det (A - iB)(s s') = det A · det(...)`.
* `RealMetaplecticGroup.proj_surjective`: every symplectic matrix is a product of two matrices of
  the big cell (`s · [[1, 0], [t, 1]]` has `det(A + t B) ≠ 0` for some `t`, since
  `det (A - iB) ≠ 0`).
-/

noncomputable section

open MeasureTheory Complex SchwartzMap Matrix Filter Topology FourierTransform
open scoped Real ContDiff RealInnerProductSpace

namespace Langlands.Theta

open Langlands.Theta.Real.Internal

variable {l : Type} [Fintype l] [DecidableEq l]

namespace Real

namespace Internal

omit [DecidableEq l] in
theorem upperPart_mul (s s' : Matrix (l ⊕ l) (l ⊕ l) ℝ) :
    automorphyUpper (s * s') = s.toBlocks₁₁.map Complex.ofReal * automorphyUpper s' + s.toBlocks₁₂.map Complex.ofReal * automorphyLower s' := by
  ext a b
  have e : ∀ x y : ℂ, x * (I * y) = I * (x * y) := fun x y => mul_left_comm x I y
  simp only [automorphyUpper, automorphyLower, Matrix.mul_apply, Matrix.add_apply, Matrix.map_apply, Matrix.toBlocks₁₁, Matrix.toBlocks₁₂,
    Matrix.of_apply, Fintype.sum_sum_type, Complex.ofReal_add, Complex.ofReal_sum, Complex.ofReal_mul, mul_sub,
    Finset.sum_sub_distrib, mul_add, Finset.mul_sum, e]
  ring

omit [DecidableEq l] in
theorem map_ofReal_mul (M N : Matrix l l ℝ) :
    (M * N).map Complex.ofReal = M.map Complex.ofReal * N.map Complex.ofReal := by
  ext i j
  simp [Matrix.mul_apply]

theorem det_map_ofReal (M : Matrix l l ℝ) : (M.map Complex.ofReal).det = (M.det : ℂ) :=
  (RingHom.map_det Complex.ofRealHom M).symm

theorem dd_mul_eq (s s' : Matrix (l ⊕ l) (l ⊕ l) ℝ) (hd : s.toBlocks₁₁.det ≠ 0) :
    automorphyDet (s * s') = (s.toBlocks₁₁.det : ℂ) *
      (automorphyUpper s' + (s.toBlocks₁₁⁻¹ * s.toBlocks₁₂).map Complex.ofReal * automorphyLower s').det := by
  have hu : IsUnit s.toBlocks₁₁.det := isUnit_iff_ne_zero.2 hd
  have hAS : s.toBlocks₁₁ * (s.toBlocks₁₁⁻¹ * s.toBlocks₁₂) = s.toBlocks₁₂ := by
    rw [← Matrix.mul_assoc, mul_nonsing_inv _ hu, Matrix.one_mul]
  have hB : s.toBlocks₁₂.map Complex.ofReal =
      s.toBlocks₁₁.map Complex.ofReal * (s.toBlocks₁₁⁻¹ * s.toBlocks₁₂).map Complex.ofReal := by
    rw [← map_ofReal_mul, hAS]
  rw [automorphyDet, upperPart_mul, hB, Matrix.mul_assoc, ← Matrix.mul_add, det_mul, det_map_ofReal]

theorem blocks_symm {A B C D : Matrix l l ℝ} (h : fromBlocks A B C D * Matrix.J l ℝ * (fromBlocks A B C D)ᵀ = Matrix.J l ℝ) :
    B * Aᵀ = A * Bᵀ := by
  have h1 := congrArg Matrix.toBlocks₁₁ h
  simp only [Matrix.J, fromBlocks_transpose, fromBlocks_multiply, toBlocks_fromBlocks₁₁] at h1
  simp only [Matrix.mul_zero, Matrix.mul_one, zero_add, add_zero, Matrix.mul_neg, Matrix.neg_mul] at h1
  exact add_neg_eq_zero.1 h1

theorem isSymm_inv_mul (s : Matrix.symplecticGroup l ℝ) (hd : s.1.toBlocks₁₁.det ≠ 0) :
    (s.1.toBlocks₁₁⁻¹ * s.1.toBlocks₁₂).IsSymm := by
  have hAB : s.1.toBlocks₁₂ * s.1.toBlocks₁₁ᵀ = s.1.toBlocks₁₁ * s.1.toBlocks₁₂ᵀ := by
    have h := SymplecticGroup.mem_iff.1 s.2
    rw [← fromBlocks_toBlocks s.1] at h
    exact blocks_symm h
  have hu : IsUnit s.1.toBlocks₁₁.det := isUnit_iff_ne_zero.2 hd
  have hut : IsUnit s.1.toBlocks₁₁ᵀ.det := by rw [det_transpose]; exact hu
  show (s.1.toBlocks₁₁⁻¹ * s.1.toBlocks₁₂)ᵀ = s.1.toBlocks₁₁⁻¹ * s.1.toBlocks₁₂
  rw [transpose_mul, transpose_nonsing_inv]
  calc s.1.toBlocks₁₂ᵀ * (s.1.toBlocks₁₁ᵀ)⁻¹
      = s.1.toBlocks₁₁⁻¹ * (s.1.toBlocks₁₁ * s.1.toBlocks₁₂ᵀ) * (s.1.toBlocks₁₁ᵀ)⁻¹ := by
        rw [← Matrix.mul_assoc, nonsing_inv_mul _ hu, Matrix.one_mul]
    _ = s.1.toBlocks₁₁⁻¹ * (s.1.toBlocks₁₂ * s.1.toBlocks₁₁ᵀ) * (s.1.toBlocks₁₁ᵀ)⁻¹ := by rw [hAB]
    _ = s.1.toBlocks₁₁⁻¹ * s.1.toBlocks₁₂ := by
        rw [Matrix.mul_assoc, Matrix.mul_assoc, mul_nonsing_inv _ hut, Matrix.mul_one]

theorem sympl_sp (s : Matrix.symplecticGroup l ℝ) (w w' : l ⊕ l → ℝ) : sympl (s.1 *ᵥ w) (s.1 *ᵥ w') = sympl w w' := by
  have h2 : s.1ᵀ * (Matrix.J l ℝ * s.1) = Matrix.J l ℝ := by
    have := SymplecticGroup.mem_iff.1 (SymplecticGroup.transpose_mem s.2)
    rwa [transpose_transpose, Matrix.mul_assoc] at this
  rw [sympl_eq, sympl_eq, mulVec_mulVec, ← Matrix.vecMul_transpose, ← dotProduct_mulVec, mulVec_mulVec, h2]

theorem sec_apply_zero (s : Matrix (l ⊕ l) (l ⊕ l) ℝ) (hA : IsUnit (blockCLM Sum.inl Sum.inl s)) (f : RealSchwartz l) :
    bigCellSection s f 0 = (((√|s.toBlocks₁₁.det|)⁻¹ : ℝ) : ℂ) *
      fourierCLM ℂ (RealSchwartz l) (chirp (-(Ring.inverse (blockCLM Sum.inl Sum.inl s) * blockCLM Sum.inl Sum.inr s)) (fourierInvCLM ℂ (RealSchwartz l) f)) 0 := by
  simp only [bigCellSection, bigCellOp, mul_apply_eq_comp, _root_.smul_apply, _root_.smul_apply, chirp_apply,
    dilation_apply hA.ringInverse, map_zero, inner_zero_left, mul_zero, ofReal_zero, zero_mul, Complex.exp_zero, one_mul,
    smul_eq_mul]

end Internal

/-- Over the big cell `det A ≠ 0` there is an element whose Schwartz operator is the explicit
operator `bigCellSection s` up to a scalar, which is `1` when `det A > 0`. -/
theorem _root_.Langlands.Theta.RealMetaplecticGroup.exists_weilSchwartz_eq_smul_bigCellSection
    (s : Matrix.symplecticGroup l ℝ) (hd : s.1.toBlocks₁₁.det ≠ 0) :
    ∃ (g : RealMetaplecticGroup l) (c : ℂ), RealMetaplecticGroup.proj g = s ∧
      RealMetaplecticGroup.weilSchwartz g = c • bigCellSection s.1 ∧
      (0 < s.1.toBlocks₁₁.det → c = 1) := by
  have hu : IsUnit s.1.toBlocks₁₁.det := isUnit_iff_ne_zero.2 hd
  let uA : (EuclideanSpace ℝ l →L[ℝ] EuclideanSpace ℝ l)ˣ :=
    ⟨Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) s.1.toBlocks₁₁, Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) s.1.toBlocks₁₁⁻¹,
      by rw [← map_mul, mul_nonsing_inv _ hu, map_one], by rw [← map_mul, nonsing_inv_mul _ hu, map_one]⟩
  have hA : IsUnit (blockCLM Sum.inl Sum.inl s.1) := ⟨uA, rfl⟩
  have hinv : Ring.inverse (blockCLM Sum.inl Sum.inl s.1) = Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) s.1.toBlocks₁₁⁻¹ :=
    Ring.inverse_unit uA
  have hAiB : Ring.inverse (blockCLM Sum.inl Sum.inl s.1) * blockCLM Sum.inl Sum.inr s.1 =
      Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) (s.1.toBlocks₁₁⁻¹ * s.1.toBlocks₁₂) := by
    rw [hinv, map_mul]
    rfl
  have hdA : (blockCLM Sum.inl Sum.inl s.1).det = s.1.toBlocks₁₁.det := det_blockCLM _ _ _
  have hdet : (Ring.inverse (blockCLM Sum.inl Sum.inl s.1)).det * (blockCLM Sum.inl Sum.inl s.1).det = 1 := by
    have := congrArg ContinuousLinearMap.det (Ring.inverse_mul_cancel _ hA)
    simpa [ContinuousLinearMap.det] using this
  set c : ℝ := (√|s.1.toBlocks₁₁.det|)⁻¹ with hcdef
  have hcsq : c ^ 2 = |s.1.toBlocks₁₁.det|⁻¹ := by
    rw [hcdef, inv_pow, Real.sq_sqrt (abs_nonneg _)]
  have hc : c ^ 2 = |(Ring.inverse (blockCLM Sum.inl Sum.inl s.1)).det| := by
    rw [hcsq, eq_inv_of_mul_eq_one_left hdet, hdA, abs_inv]
  have hc0 : c ≠ 0 := inv_ne_zero (Real.sqrt_pos.2 (abs_pos.2 hd)).ne'
  obtain ⟨z, hz1, hz, hzpos⟩ : ∃ z : ℂ, ‖z‖ = 1 ∧ z ^ 2 * ((c : ℂ) ^ 2 * (s.1.toBlocks₁₁.det : ℂ)) = 1 ∧
      (0 < s.1.toBlocks₁₁.det → z = 1) := by
    by_cases hpos : 0 < s.1.toBlocks₁₁.det
    · have e : c ^ 2 * s.1.toBlocks₁₁.det = 1 := by
        rw [hcsq, abs_of_pos hpos, inv_mul_cancel₀ hpos.ne']
      refine ⟨1, by simp, ?_, fun _ => rfl⟩
      have e2 : ((c : ℂ) ^ 2 * (s.1.toBlocks₁₁.det : ℂ)) = ((c ^ 2 * s.1.toBlocks₁₁.det : ℝ) : ℂ) := by push_cast; ring
      rw [e2, e]
      simp
    · have hneg : s.1.toBlocks₁₁.det < 0 := lt_of_le_of_ne (not_lt.1 hpos) hd
      have e : c ^ 2 * s.1.toBlocks₁₁.det = -1 := by
        rw [hcsq, abs_of_neg hneg, inv_neg, neg_mul, inv_mul_cancel₀ hd]
      refine ⟨I, by simp, ?_, fun h => absurd h hpos⟩
      have e2 : ((c : ℂ) ^ 2 * (s.1.toBlocks₁₁.det : ℂ)) = ((c ^ 2 * s.1.toBlocks₁₁.det : ℝ) : ℂ) := by push_cast; ring
      rw [e2, e, I_sq]
      push_cast
      ring
  have hz0 : z ≠ 0 := fun h => by simp [h] at hz1
  have hU : IsUnit (z • bigCellSection s.1) := by
    rw [Algebra.smul_def]
    exact ((IsUnit.mk0 z hz0).map _).mul (isUnit_bigCellOp hA.ringInverse _ _ hc0)
  have hiso := isL2Isometry_bigCellOp hA.ringInverse (blockCLM Sum.inl Sum.inr s.1) (blockCLM Sum.inr Sum.inl s.1) hc
  have hI : Intertwines (fun w => s.1 *ᵥ w) (z • bigCellSection s.1).toLinearMap := by
    refine Intertwines.of_rhoFun (fun f => ?_) (fun w => (intw_of_sympl (sympl_sp s) hA c w).smul z)
    show ‖schwartzToL2 l ((z • bigCellSection s.1) f)‖ = ‖schwartzToL2 l f‖
    rw [_root_.smul_apply, map_smul, norm_smul, hz1, one_mul]
    exact hiso f
  have hN : IsNormalizedLift s.1 (z • bigCellSection s.1) := by
    intro s' f hf
    have key := isNormalizedLift_unipotent _ (isSymm_inv_mul s hd) s' f hf
    have ev : (z • bigCellSection s.1) f 0 = z * ((c : ℂ) *
        fourierCLM ℂ (RealSchwartz l) (chirp (-(Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) (s.1.toBlocks₁₁⁻¹ * s.1.toBlocks₁₂))) (fourierInvCLM ℂ (RealSchwartz l) f)) 0) := by
      rw [_root_.smul_apply, _root_.smul_apply, smul_eq_mul, sec_apply_zero s.1 hA f, hAiB]
    rw [ev, dd_mul_eq s.1 s'.1 hd, ← key]
    calc _ = (z ^ 2 * ((c : ℂ) ^ 2 * (s.1.toBlocks₁₁.det : ℂ))) *
          ((fourierCLM ℂ (RealSchwartz l) (chirp (-(Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) (s.1.toBlocks₁₁⁻¹ * s.1.toBlocks₁₂))) (fourierInvCLM ℂ (RealSchwartz l) f)) 0) ^ 2 *
            (automorphyUpper s'.1 + (s.1.toBlocks₁₁⁻¹ * s.1.toBlocks₁₂).map Complex.ofReal * automorphyLower s'.1).det) := by ring
      _ = _ := by rw [hz, one_mul]
  obtain ⟨g, hg1, hg2⟩ := RealMetaplecticGroup.exists_of_intertwines_of_isNormalizedLift s hU hI hN
  exact ⟨g, z, hg1, hg2, hzpos⟩

namespace Internal

def lo (t : ℝ) : Matrix (l ⊕ l) (l ⊕ l) ℝ := fromBlocks 1 0 (t • 1) 1

theorem lo_mem (t : ℝ) : lo (l := l) t ∈ Matrix.symplecticGroup l ℝ := by
  rw [SymplecticGroup.mem_iff, lo, Matrix.J, fromBlocks_transpose, fromBlocks_multiply, fromBlocks_multiply]
  simp

theorem lo_mul (t : ℝ) : lo (l := l) t * lo (-t) = 1 := by
  rw [lo, lo, fromBlocks_multiply]
  simp

theorem toBlocks₁₁_mul_lo (s : Matrix (l ⊕ l) (l ⊕ l) ℝ) (t : ℝ) : (s * lo t).toBlocks₁₁ = s.toBlocks₁₁ + t • s.toBlocks₁₂ := by
  conv_lhs => rw [← fromBlocks_toBlocks s, lo, fromBlocks_multiply, toBlocks_fromBlocks₁₁]
  simp

theorem exists_det_ne (s : Matrix (l ⊕ l) (l ⊕ l) ℝ) (h : automorphyDet s ≠ 0) : ∃ t : ℝ, (s.toBlocks₁₁ + t • s.toBlocks₁₂).det ≠ 0 := by
  let M : Matrix l l (Polynomial ℝ) := Matrix.of fun a b =>
    Polynomial.C (s (.inl a) (.inl b)) + Polynomial.X * Polynomial.C (s (.inl a) (.inr b))
  have hev : ∀ t : ℝ, Polynomial.eval t M.det = (s.toBlocks₁₁ + t • s.toBlocks₁₂).det := fun t => by
    have e : Polynomial.eval t M.det = ((Polynomial.evalRingHom t).mapMatrix M).det :=
      RingHom.map_det (Polynomial.evalRingHom t) M
    rw [e]
    congr 1
    ext a b
    simp [M, Matrix.toBlocks₁₁, Matrix.toBlocks₁₂]
    ring
  have hev' : Polynomial.eval₂ Complex.ofRealHom (-I) M.det = automorphyDet s := by
    have e : Polynomial.eval₂ Complex.ofRealHom (-I) M.det =
        ((Polynomial.eval₂RingHom Complex.ofRealHom (-I)).mapMatrix M).det :=
      RingHom.map_det (Polynomial.eval₂RingHom Complex.ofRealHom (-I)) M
    rw [e, automorphyDet]
    congr 1
    ext a b
    simp [M, automorphyUpper]
    ring
  have hP : M.det ≠ 0 := fun h0 => h (by rw [← hev', h0, Polynomial.eval₂_zero])
  by_contra hall
  push Not at hall
  apply hP
  apply Polynomial.eq_zero_of_infinite_isRoot
  convert Set.infinite_univ (α := ℝ)
  ext t
  simp only [Set.mem_ofPred_eq, Polynomial.IsRoot.def, hev, hall, Set.mem_univ]

end Internal

/-- The projection to `Sp_{2l}(ℝ)` is surjective. -/
theorem _root_.Langlands.Theta.RealMetaplecticGroup.proj_surjective :
    Function.Surjective (RealMetaplecticGroup.proj : RealMetaplecticGroup l → _) := by
  intro s
  obtain ⟨t, ht⟩ := exists_det_ne s.1 (automorphyDet_ne_zero s)
  let n : Matrix.symplecticGroup l ℝ := ⟨lo t, lo_mem t⟩
  let m : Matrix.symplecticGroup l ℝ := ⟨lo (-t), lo_mem (-t)⟩
  have e1 : (s * n).1.toBlocks₁₁.det ≠ 0 := by
    show (s.1 * lo t).toBlocks₁₁.det ≠ 0
    rw [toBlocks₁₁_mul_lo]
    exact ht
  have e2 : m.1.toBlocks₁₁.det ≠ 0 := by
    show (lo (l := l) (-t)).toBlocks₁₁.det ≠ 0
    simp [lo]
  obtain ⟨g1, -, hg1, -⟩ := RealMetaplecticGroup.exists_weilSchwartz_eq_smul_bigCellSection (s * n) e1
  obtain ⟨g2, -, hg2, -⟩ := RealMetaplecticGroup.exists_weilSchwartz_eq_smul_bigCellSection m e2
  refine ⟨g1 * g2, ?_⟩
  have hnm : n * m = 1 := Subtype.ext (lo_mul t)
  rw [map_mul, hg1, hg2, mul_assoc, hnm, mul_one]

end Real

end Langlands.Theta
