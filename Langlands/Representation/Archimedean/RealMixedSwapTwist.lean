import Langlands.Representation.Archimedean.StandardModule

/-!
# A signed reversal on real rank-three function spaces

The signed reversal has determinant one and exchanges the two adjacent rotation planes.
It gives a smooth involution on functions by inverse transpose and left multiplication.
-/

noncomputable section

open scoped Matrix Matrix.Norms.Operator Manifold ContDiff

namespace Langlands.Archimedean.RealMixedSwapTwist

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

abbrev G := Langlands.GeneralLinear 3 ℝ
abbrev A := Matrix (Fin 3) (Fin 3) ℝ

/-- The determinant-one signed reversal of three coordinates. -/
def wMat : A := !![0, 0, 1; 0, -1, 0; 1, 0, 0]

theorem wMat_mul_self : wMat * wMat = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [wMat, Matrix.mul_apply, Fin.sum_univ_succ]

theorem wMat_transpose : wMatᵀ = wMat := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem det_wMat : wMat.det = 1 := by
  norm_num [wMat, Matrix.det_fin_three]

/-- The signed reversal as an invertible matrix. -/
def w : G := ⟨wMat, wMat, wMat_mul_self, wMat_mul_self⟩

@[simp] theorem w_val : (w : A) = wMat := rfl

theorem w_mul_self : w * w = 1 := Units.ext wMat_mul_self

theorem w_inv : w⁻¹ = w := inv_eq_of_mul_eq_one_right w_mul_self

theorem w_mem : w ∈ unitaryCompact ℝ 3 := by
  rw [mem_unitaryCompact_iff]
  change star wMat * wMat = 1
  rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial,
    wMat_transpose, wMat_mul_self]

/-- Transposition of a real invertible matrix. -/
def transposeGL (g : G) : G :=
  ⟨(g : A)ᵀ, (↑g⁻¹ : A)ᵀ,
    by rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one],
    by rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]⟩

@[simp] theorem transposeGL_val (g : G) : (transposeGL g : A) = (g : A)ᵀ := rfl

theorem transposeGL_mul (g h : G) :
    transposeGL (g * h) = transposeGL h * transposeGL g := by
  apply Units.ext
  simp only [transposeGL_val, Units.val_mul, Matrix.transpose_mul]

theorem transposeGL_transposeGL (g : G) : transposeGL (transposeGL g) = g :=
  Units.ext (Matrix.transpose_transpose _)

theorem transposeGL_inv (g : G) : transposeGL g⁻¹ = (transposeGL g)⁻¹ :=
  Units.ext rfl

theorem transposeGL_w : transposeGL w = w := Units.ext wMat_transpose

/-- The inverse-transpose automorphism. -/
def theta : G →* G where
  toFun g := (transposeGL g)⁻¹
  map_one' := by
    have h : transposeGL (1 : G) = 1 :=
      Units.ext (by simp only [transposeGL_val, Units.val_one, Matrix.transpose_one])
    rw [h, inv_one]
  map_mul' g h := by rw [transposeGL_mul, mul_inv_rev]

theorem theta_apply (g : G) : theta g = (transposeGL g)⁻¹ := rfl

theorem theta_theta (g : G) : theta (theta g) = g := by
  rw [theta_apply, theta_apply, transposeGL_inv, inv_inv, transposeGL_transposeGL]

theorem theta_w : theta w = w := by rw [theta_apply, transposeGL_w, w_inv]

/-- Inverse transpose is the identity on the real orthogonal group. -/
theorem theta_compact {k : G} (hk : k ∈ unitaryCompact ℝ 3) : theta k = k := by
  apply inv_injective
  rw [theta_apply, inv_inv]
  apply Units.ext
  have h := (mem_unitaryCompact_iff ℝ 3 k).mp hk
  rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] at h
  change (k : A)ᵀ = (↑k⁻¹ : A)
  calc
    (k : A)ᵀ = (k : A)ᵀ * ((k : A) * (↑k⁻¹ : A)) := by rw [Units.mul_inv, mul_one]
    _ = (↑k⁻¹ : A) := by rw [← mul_assoc, h, one_mul]

/-- The signed one-sided reversal `g ↦ w (gᵀ)⁻¹`. -/
def twist (g : G) : G := w * theta g

theorem twist_mul (g h : G) : twist (g * h) = twist g * theta h := by
  simp only [twist, map_mul, mul_assoc]

theorem twist_twist (g : G) : twist (twist g) = g := by
  simp only [twist, map_mul, theta_w, theta_theta, ← mul_assoc, w_mul_self, one_mul]

theorem twist_mul_compact (g : G) {k : G} (hk : k ∈ unitaryCompact ℝ 3) :
    twist (g * k) = twist g * k := by rw [twist_mul, theta_compact hk]

theorem contMDiff_transposeGL :
    ContMDiff (matrixModel ℝ 3) (matrixModel ℝ 3) ∞ transposeGL := by
  apply ContMDiff.of_comp_isOpenEmbedding Units.isOpenEmbedding_val
  exact ((Matrix.transposeLinearEquiv (Fin 3) (Fin 3) ℝ ℝ).toContinuousLinearEquiv :
    A →L[ℝ] A).contDiff.contMDiff.comp Units.contMDiff_val

theorem contMDiff_theta : ContMDiff (matrixModel ℝ 3) (matrixModel ℝ 3) ∞ theta :=
  contMDiff_transposeGL.inv

theorem contMDiff_twist : ContMDiff (matrixModel ℝ 3) (matrixModel ℝ 3) ∞ twist :=
  contMDiff_const.mul contMDiff_theta

/-- Pullback of functions along the signed reversal. -/
def twistLin : (G → ℂ) →ₗ[ℂ] (G → ℂ) := LinearMap.funLeft ℂ ℂ twist

@[simp] theorem twistLin_apply (f : G → ℂ) (g : G) : twistLin f g = f (twist g) := rfl

theorem twistLin_twistLin (f : G → ℂ) : twistLin (twistLin f) = f := by
  funext g
  simp only [twistLin_apply, twist_twist]

theorem contMDiff_twistLin {f : G → ℂ}
    (hf : ContMDiff (matrixModel ℝ 3) 𝓘(ℝ, ℂ) ∞ f) :
    ContMDiff (matrixModel ℝ 3) 𝓘(ℝ, ℂ) ∞ (twistLin f) :=
  hf.comp contMDiff_twist

theorem rightTranslation_twistLin (f : G → ℂ) (k : unitaryCompact ℝ 3) :
    Whittaker.rightTranslation ℂ G (k : G) (twistLin f) =
      twistLin (Whittaker.rightTranslation ℂ G (k : G) f) := by
  funext g
  change f (twist (g * k)) = f (twist g * k)
  rw [twist_mul_compact g k.2]

/-- Pullback preserves orthogonal finite functions. -/
theorem twistLin_mem_kFiniteVectors {f : G → ℂ}
    (hf : f ∈ kFiniteVectors (Whittaker.rightTranslation ℂ G) (unitaryCompact ℝ 3)) :
    twistLin f ∈ kFiniteVectors (Whittaker.rightTranslation ℂ G) (unitaryCompact ℝ 3) := by
  refine (mem_kFiniteVectors_iff _ _ _).mpr ?_
  have hfin := (mem_kFiniteVectors_iff _ _ _).mp hf
  refine Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ (Set.range
    fun k : unitaryCompact ℝ 3 => Whittaker.rightTranslation ℂ G (k : G) f)).map twistLin) ?_
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨k, rfl⟩
  exact ⟨_, Submodule.subset_span ⟨k, rfl⟩, (rightTranslation_twistLin f k).symm⟩

theorem wMat_rotationGenerator (p : Fin 2) :
    wMat * rotationGenerator 3 p * wMat = rotationGenerator 3 (1 - p.val) := by
  fin_cases p <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [wMat, rotationGenerator, Matrix.mul_apply, Fin.sum_univ_succ,
      Matrix.vecHead, Matrix.vecTail]

/-- Signed reversal exchanges the adjacent rotation planes with the angle unchanged. -/
theorem w_blockRotation_w (p : Fin 2) (t : ℝ) :
    w * blockRotation 3 p t * w = blockRotation 3 (1 - p.val) t := by
  apply Units.ext
  change wMat * NormedSpace.exp (t • rotationGenerator 3 p) * wMat =
    NormedSpace.exp (t • rotationGenerator 3 (1 - p.val))
  have h := Matrix.exp_units_conj w (t • rotationGenerator 3 p)
  rw [w_inv, w_val, mul_smul_comm, smul_mul_assoc,
    wMat_rotationGenerator] at h
  exact h.symm

theorem twist_blockRotation_mul (p : Fin 2) (t : ℝ) (g : G) :
    twist (blockRotation 3 p t * g) =
      blockRotation 3 (1 - p.val) t * twist g := by
  simp only [twist, map_mul, theta_compact (blockRotation_mem_unitaryCompact 3 p t)]
  have h := w_blockRotation_w p t
  calc
    w * (blockRotation 3 p t * theta g) =
        (w * blockRotation 3 p t * w) * (w * theta g) := by
          simp only [mul_assoc, ← mul_assoc w w, w_mul_self, one_mul]
    _ = blockRotation 3 (1 - p.val) t * (w * theta g) := by rw [h]

/-- Pullback exchanges the two Fourier conditions, including every Fourier index. -/
theorem blockFourierCoefficient_twistLin (p : Fin 2) (k : ℤ) (f : G → ℂ) (g : G) :
    blockFourierCoefficient 3 p k (twistLin f) g =
      blockFourierCoefficient 3 (1 - p.val) k f (twist g) := by
  unfold blockFourierCoefficient
  simp only [twistLin_apply, twist_blockRotation_mul]

end Langlands.Archimedean.RealMixedSwapTwist
