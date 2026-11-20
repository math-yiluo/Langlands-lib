import Mathlib.Analysis.Real.Sqrt
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Matrix.Bilinear
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.StdBasis

/-! # Normalized off-block determinants -/

noncomputable section

set_option autoImplicit false

open Matrix
open scoped Kronecker

namespace Langlands.Archimedean.RealCartanOffBlockDeterminant

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

private def blockMul (A : Matrix ι ι ℝ) (B : Matrix κ κ ℝ) :
    Module.End ℝ (Matrix ι κ ℝ) :=
  (mulRightLinearMap ι ℝ B).comp (mulLeftLinearMap κ ℝ A)

/-- The action `X ↦ g⁻¹ X h` on a rectangular block. -/
def offBlockAction (g : (Matrix ι ι ℝ)ˣ) (h : (Matrix κ κ ℝ)ˣ) :
    Matrix ι κ ℝ ≃ₗ[ℝ] Matrix ι κ ℝ :=
  { blockMul g⁻¹.val h.val with
    invFun := blockMul g.val h⁻¹.val
    left_inv := fun X => calc
      g.val * (g⁻¹.val * X * h.val) * h⁻¹.val =
          (g.val * g⁻¹.val) * X * (h.val * h⁻¹.val) := by simp only [Matrix.mul_assoc]
      _ = X := by simp
    right_inv := fun X => calc
      g⁻¹.val * (g.val * X * h⁻¹.val) * h.val =
          (g⁻¹.val * g.val) * X * (h⁻¹.val * h.val) := by simp only [Matrix.mul_assoc]
      _ = X := by simp }

@[simp]
theorem offBlockAction_apply (g : (Matrix ι ι ℝ)ˣ) (h : (Matrix κ κ ℝ)ˣ)
    (X : Matrix ι κ ℝ) : offBlockAction g h X = g⁻¹.val * X * h.val := rfl

@[simp]
theorem offBlockAction_symm_apply (g : (Matrix ι ι ℝ)ˣ) (h : (Matrix κ κ ℝ)ˣ)
    (X : Matrix ι κ ℝ) : (offBlockAction g h).symm X = g.val * X * h⁻¹.val := rfl

omit [DecidableEq ι] [DecidableEq κ] in
private theorem stdBasis_repr (X : Matrix ι κ ℝ) (i : ι) (j : κ) :
    (stdBasis ℝ ι κ).repr X (i, j) = X i j := by
  simp [stdBasis, Pi.basis_repr]

private theorem blockMul_toMatrix_apply (A : Matrix ι ι ℝ) (B : Matrix κ κ ℝ)
    (i p : ι) (j q : κ) :
    LinearMap.toMatrix (stdBasis ℝ ι κ) (stdBasis ℝ ι κ) (blockMul A B) (i, j) (p, q) =
      A i p * B q j := by
  rw [LinearMap.toMatrix_apply, stdBasis_eq_single, stdBasis_repr]
  change (A * single p q (1 : ℝ) * B) i j = _
  have hs (k : κ) : (A * single p q (1 : ℝ)) i k = if k = q then A i p else 0 := by
    rw [Matrix.mul_apply]
    by_cases hk : k = q
    · subst k
      simp [single_apply, mul_ite]
    · simp [hk, Ne.symm hk]
  rw [Matrix.mul_apply]
  simp [hs, ite_mul]

/-- The determinant contribution of the off-block action is the product of the
block determinants with the rectangular multiplicities. -/
theorem det_offBlockAction (g : (Matrix ι ι ℝ)ˣ) (h : (Matrix κ κ ℝ)ˣ) :
    LinearMap.det (offBlockAction g h : Module.End ℝ (Matrix ι κ ℝ)) =
      (det g⁻¹.val) ^ Fintype.card κ * (det h.val) ^ Fintype.card ι := by
  rw [← LinearMap.det_toMatrix (stdBasis ℝ ι κ)]
  have he : LinearMap.toMatrix (stdBasis ℝ ι κ) (stdBasis ℝ ι κ)
      (offBlockAction g h).toLinearMap = g⁻¹.val ⊗ₖ h.valᵀ := by
    ext ⟨i, j⟩ ⟨p, q⟩
    exact blockMul_toMatrix_apply g⁻¹.val h.val i p j q
  rw [he, det_kronecker, det_transpose]

private theorem blockMul_toMatrix_swap (A : Matrix ι ι ℝ) (B : Matrix κ κ ℝ) :
    LinearMap.toMatrix (stdBasis ℝ κ ι) (stdBasis ℝ κ ι) (blockMul B A) =
      reindex (Equiv.prodComm ι κ) (Equiv.prodComm ι κ)
        (LinearMap.toMatrix (stdBasis ℝ ι κ) (stdBasis ℝ ι κ) (blockMul A B))ᵀ := by
  ext ⟨j, i⟩ ⟨q, p⟩
  change LinearMap.toMatrix (stdBasis ℝ κ ι) (stdBasis ℝ κ ι) (blockMul B A) (j, i) (q, p) =
    LinearMap.toMatrix (stdBasis ℝ ι κ) (stdBasis ℝ ι κ) (blockMul A B) (p, q) (i, j)
  simp only [blockMul_toMatrix_apply, mul_comm]

private theorem det_blockMul_swap (A : Matrix ι ι ℝ) (B : Matrix κ κ ℝ) :
    LinearMap.det (blockMul B A) = LinearMap.det (blockMul A B) ∧
      LinearMap.det (1 - blockMul B A) = LinearMap.det (1 - blockMul A B) := by
  let e := reindexRingEquiv ℝ (Equiv.prodComm ι κ)
  let T := LinearMap.toMatrix (stdBasis ℝ ι κ) (stdBasis ℝ ι κ) (blockMul A B)
  have he := blockMul_toMatrix_swap A B
  constructor
  · rw [← LinearMap.det_toMatrix (stdBasis ℝ κ ι), ← LinearMap.det_toMatrix (stdBasis ℝ ι κ),
      he, det_reindex_self, det_transpose]
  · rw [← LinearMap.det_toMatrix (stdBasis ℝ κ ι), ← LinearMap.det_toMatrix (stdBasis ℝ ι κ),
      map_sub, map_sub, LinearMap.toMatrix_one, LinearMap.toMatrix_one, he]
    change det (1 - e Tᵀ) = det (1 - T)
    calc
      _ = det (e (1 - Tᵀ)) := by rw [map_sub, map_one]
      _ = det ((1 - T)ᵀ) := by
        rw [show ⇑e = reindex (Equiv.prodComm ι κ) (Equiv.prodComm ι κ) from rfl,
          det_reindex_self, transpose_sub, transpose_one]
      _ = _ := det_transpose _

omit [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] in
private theorem det_symm (L : Matrix ι κ ℝ ≃ₗ[ℝ] Matrix ι κ ℝ) :
    LinearMap.det L.symm.toLinearMap = (LinearMap.det L.toLinearMap)⁻¹ := by
  simpa only [Units.val_inv_eq_inv_val, LinearEquiv.coe_det] using
    (LinearEquiv.coe_inv_det L).symm

omit [DecidableEq ι] [DecidableEq κ] in
private theorem abs_det_one_sub_symm (L : Matrix ι κ ℝ ≃ₗ[ℝ] Matrix ι κ ℝ) :
    |LinearMap.det (1 - L.symm.toLinearMap)| =
      |LinearMap.det L.toLinearMap|⁻¹ * |LinearMap.det (1 - L.toLinearMap)| := by
  have hcomp : L.symm.toLinearMap * L.toLinearMap = 1 := by
    apply LinearMap.ext
    intro X
    exact L.symm_apply_apply X
  have hfact : (1 - L.symm.toLinearMap) = L.symm.toLinearMap * (-(1 - L.toLinearMap)) := by
    rw [neg_sub, mul_sub, hcomp, mul_one]
  rw [hfact, map_mul, abs_mul, det_symm, abs_inv, ← neg_one_smul ℝ,
    LinearMap.det_smul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]

/-- The absolute denominator contributed by the two blocks after modulus normalization. -/
def normalizedOffBlockDet (g : (Matrix ι ι ℝ)ˣ) (h : (Matrix κ κ ℝ)ˣ) : ℝ :=
  let L := (offBlockAction g h).toLinearMap
  |LinearMap.det (1 - L)| / Real.sqrt |LinearMap.det L|

/-- The normalized off-block determinant is independent of the order of a pair. -/
def RealCartanOffBlockDeterminantStatement (ι κ : Type*) [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] : Prop :=
  ∀ (g : (Matrix ι ι ℝ)ˣ) (h : (Matrix κ κ ℝ)ˣ),
    normalizedOffBlockDet h g = normalizedOffBlockDet g h

theorem normalizedOffBlockDet_swap : RealCartanOffBlockDeterminantStatement ι κ := by
  intro g h
  let L := offBlockAction g h
  obtain ⟨hdet, hsub⟩ := det_blockMul_swap g.val h⁻¹.val
  change LinearMap.det (offBlockAction h g).toLinearMap = LinearMap.det L.symm.toLinearMap at hdet
  change LinearMap.det (1 - (offBlockAction h g).toLinearMap) =
    LinearMap.det (1 - L.symm.toLinearMap) at hsub
  unfold normalizedOffBlockDet
  dsimp only
  rw [hdet, hsub, abs_det_one_sub_symm, det_symm, abs_inv, Real.sqrt_inv]
  let d := |LinearMap.det L.toLinearMap|
  let w := |LinearMap.det (1 - L.toLinearMap)|
  have hd : 0 < d := by
    apply abs_pos.mpr
    rw [← LinearEquiv.coe_det]
    exact (LinearEquiv.det L).ne_zero
  have hs := Real.sq_sqrt hd.le
  have hs0 := (Real.sqrt_pos.2 hd).ne'
  change (d⁻¹ * w) / (Real.sqrt d)⁻¹ = w / Real.sqrt d
  field_simp [hd.ne', hs0]
  nlinarith [congrArg (w * ·) hs]

end Langlands.Archimedean.RealCartanOffBlockDeterminant
