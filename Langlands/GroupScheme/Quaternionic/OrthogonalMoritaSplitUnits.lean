import Langlands.GroupScheme.Quaternionic.DegreeSplittingMatrix
import Langlands.GroupScheme.Quaternionic.QuaternionicMoritaIsometryProof
import Langlands.GroupScheme.OrthogonalMatrix.Comparison

/-! # The arbitrary-degree split Gram matrix and isometry units -/

noncomputable section
universe u
open Matrix Module
open scoped TensorProduct

namespace Langlands.GroupScheme.Quaternionic.OrthogonalMorita

open DegreeSplitting

variable {K D L : Type u} [Field K] [DivisionRing D] [Algebra K D]
  [Field L] [Algebra K L]
  {ι : Type} [Fintype ι] [DecidableEq ι]
  {κ : Type} [Fintype κ] [DecidableEq κ]
  (e : L ⊗[K] D ≃ₐ[L] Matrix ι ι L)
  [FiniteDimensional K D] (σ : FirstKindInvolution K D)
  (hσ : finrank K σ.symmetricSubspace = Fintype.card ι * (Fintype.card ι + 1) / 2)

include hσ in
/-- The polar matrix of the split quadratic Gram matrix. -/
theorem splitGram_add_transpose (Q : Matrix κ κ D) :
    splitGram e σ Q + (splitGram e σ Q)ᵀ =
      matrixChartR (n := κ) e L (1 ⊗ₜ[K] (Q + σ.matrix κ Q)) * blockInvolutionMatrix e σ := by
  have h := matrixChartL_baseChange e σ (1 ⊗ₜ[K] Q)
  rw [FirstKindInvolution.baseChange_tmul] at h
  rw [TensorProduct.tmul_add, _root_.map_add, Matrix.add_mul, h, splitGram,
    Matrix.transpose_mul, transpose_blockInvolutionMatrix e σ hσ]
  congr 1
  rw [Matrix.mul_assoc, blockInvolutionMatrix_inv_mul, Matrix.mul_one]

include hσ in
/-- Nondegeneracy of the original quadratic class gives a unit split polar matrix. -/
theorem isUnit_splitGram_polar (q : σ.QuadraticForms κ)
    (Q : Matrix κ κ D) (hQ : (Submodule.Quotient.mk Q : σ.QuadraticForms κ) = q)
    (hq : σ.IsNondegenerateQuadratic q) : IsUnit (splitGram e σ Q + (splitGram e σ Q)ᵀ) := by
  rw [splitGram_add_transpose e σ hσ]
  unfold FirstKindInvolution.IsNondegenerateQuadratic at hq
  rw [← hQ, FirstKindInvolution.polar_mk] at hq
  refine IsUnit.mul ?_ ?_
  · exact (hq.map (Algebra.TensorProduct.includeRight :
      Matrix κ κ D →ₐ[K] L ⊗[K] Matrix κ κ D)).map (matrixChartR (n := κ) e L)
  · exact ⟨⟨_, _, blockInvolutionMatrix_mul_inv e σ, blockInvolutionMatrix_inv_mul e σ⟩, rfl⟩

variable (R : Type u) [CommRing R] [Algebra K R] [Algebra L R] [IsScalarTower K L R]

include hσ in
/-- Isometry units are exactly matrices with alternating split Gram defect. -/
theorem mem_isometryUnits_split_iff (Q : Matrix κ κ D) (y : (R ⊗[K] Matrix κ κ D)ˣ) :
    y ∈ σ.isometryUnits Q R ↔ OrthogonalMatrix.IsAlt
      (matrixChartR (n := κ) e R y * (splitGram e σ Q).map (algebraMap L R) *
        (matrixChartR (n := κ) e R y)ᵀ - (splitGram e σ Q).map (algebraMap L R)) := by
  have hSS' := OrthogonalMatrix.map_mul_map_eq_one R
    (blockInvolutionMatrix_mul_inv e σ (n := κ))
  have hS'S := OrthogonalMatrix.map_mul_map_eq_one R
    (blockInvolutionMatrix_inv_mul e σ (n := κ))
  have hS : ((blockInvolutionMatrix e σ (n := κ)).map (algebraMap L R))ᵀ =
      (blockInvolutionMatrix e σ).map (algebraMap L R) := by
    rw [← Matrix.transpose_map, transpose_blockInvolutionMatrix e σ hσ]
  change IsometryCut.defect (σ.matrix κ) Q (y : R ⊗[K] Matrix κ κ D) ∈
    (σ.matrix κ).alternatingSubspace.baseChange R ↔ _
  rw [IsometryCut.alternatingSubspace_baseChange, Submodule.restrictScalars_mem,
    FirstKindInvolution.mem_alternatingSubspace, IsometryCut.defect,
    MoritaIsometry.exists_sub_eq_defect_iff (Φ := matrixChartR (n := κ) e R)
      (τ := (σ.matrix κ).baseChange R) (matrixChartR_baseChange e σ R) hSS' hS'S hS,
    splitGram, Matrix.map_mul, ← matrixChartR_one_tmul]
  rfl

section Conjugation

variable {n : ℕ}
  (P : Matrix (Fin n ⊕ Fin n) (κ × ι) L)
  (P' : Matrix (κ × ι) (Fin n ⊕ Fin n) L)

/-- The matrix chart followed by the supplied basis conjugation. -/
def conjugatedMatrix (a : R ⊗[K] Matrix κ κ D) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R :=
  P.map (algebraMap L R) * matrixChartR (n := κ) e R a * P'.map (algebraMap L R)

omit [FiniteDimensional K D] in
theorem conjugatedMatrix_one (hPP' : P * P' = 1) :
    conjugatedMatrix e R P P' 1 = 1 := by
  rw [conjugatedMatrix, _root_.map_one, Matrix.mul_one]
  exact OrthogonalMatrix.map_mul_map_eq_one R hPP'

omit [FiniteDimensional K D] in
theorem conjugatedMatrix_mul (hP'P : P' * P = 1) (a b : R ⊗[K] Matrix κ κ D) :
    conjugatedMatrix e R P P' (a * b) =
      conjugatedMatrix e R P P' a * conjugatedMatrix e R P P' b := by
  have h := OrthogonalMatrix.map_mul_map_eq_one R hP'P
  simp only [conjugatedMatrix, _root_.map_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (P'.map _) (P.map _), h, Matrix.one_mul]

omit [FiniteDimensional K D] in
theorem conjugatedMatrix_injective (hP'P : P' * P = 1) :
    Function.Injective (conjugatedMatrix e R P P') := by
  intro a b hab
  have h := OrthogonalMatrix.map_mul_map_eq_one R hP'P
  apply (matrixChartR (n := κ) e R).injective
  have h' := congrArg (fun M => P'.map (algebraMap L R) * M * P.map (algebraMap L R)) hab
  simp only [conjugatedMatrix, Matrix.mul_assoc] at h'
  simpa only [← Matrix.mul_assoc (P'.map _) (P.map _), h, Matrix.one_mul,
    Matrix.mul_one] using h'

variable (Q : Matrix κ κ D) (hPP' : P * P' = 1) (hP'P : P' * P = 1)
  (hPQ : OrthogonalMatrix.IsAlt (P * splitGram e σ Q * Pᵀ -
    OrthogonalMatrix.formMatrix (Fin n) L))

include hσ hP'P hPQ in
/-- Conjugation by a hyperbolic basis transports the exact isometry condition. -/
theorem conjugatedMatrix_mem_iff (y : (R ⊗[K] Matrix κ κ D)ˣ) :
    conjugatedMatrix e R P P' y ∈ OrthogonalMatrix.orthogonalGroup (Fin n) R ↔
      y ∈ σ.isometryUnits Q R := by
  have hPQ' := hPQ.map (algebraMap L R)
  rw [Matrix.map_sub _ (_root_.map_sub _), Matrix.map_mul, Matrix.map_mul,
    Matrix.transpose_map, OrthogonalMatrix.formMatrix_map] at hPQ'
  rw [mem_isometryUnits_split_iff e σ hσ, OrthogonalMatrix.mem_orthogonalGroup_iff,
    OrthogonalMatrix.defect, conjugatedMatrix]
  exact OrthogonalMatrix.isAlt_conj_sub_iff
    (OrthogonalMatrix.map_mul_map_eq_one R hP'P) hPQ' _

include hσ in
/-- Isometry units map to split orthogonal matrices by the actual conjugated chart. -/
def splitUnitsHom : σ.isometryUnits Q R →* OrthogonalMatrix.orthogonalGroup (Fin n) R where
  toFun y := ⟨conjugatedMatrix e R P P' y.1,
    (conjugatedMatrix_mem_iff e σ hσ R P P' Q hP'P hPQ y).2 y.2⟩
  map_one' := Subtype.ext (conjugatedMatrix_one e R P P' hPP')
  map_mul' _a _b := Subtype.ext (conjugatedMatrix_mul e R P P' hP'P _ _)

include hσ in
theorem splitUnitsHom_bijective :
    Function.Bijective (splitUnitsHom e σ hσ R P P' Q hPP' hP'P hPQ) := by
  constructor
  · intro a b hab
    apply Subtype.ext
    apply Units.ext
    exact conjugatedMatrix_injective e R P P' hP'P (congrArg Subtype.val hab)
  · intro g
    have hPP'R := OrthogonalMatrix.map_mul_map_eq_one R hPP'
    have hP'PR := OrthogonalMatrix.map_mul_map_eq_one R hP'P
    set PR := P.map (algebraMap L R)
    set P'R := P'.map (algebraMap L R)
    set gm : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R := (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R)
    set gi := OrthogonalMatrix.invMatrix gm
    have hggi : gm * gi = 1 := OrthogonalMatrix.mul_invMatrix g.2
    have hgig : gi * gm = 1 := OrthogonalMatrix.invMatrix_mul g.2
    let gu : (Matrix (κ × ι) (κ × ι) R)ˣ :=
      { val := P'R * gm * PR
        inv := P'R * gi * PR
        val_inv := by
          simp only [Matrix.mul_assoc]
          rw [← Matrix.mul_assoc PR P'R, hPP'R, Matrix.one_mul,
            ← Matrix.mul_assoc gm gi, hggi, Matrix.one_mul, hP'PR]
        inv_val := by
          simp only [Matrix.mul_assoc]
          rw [← Matrix.mul_assoc PR P'R, hPP'R, Matrix.one_mul,
            ← Matrix.mul_assoc gi, hgig, Matrix.one_mul, hP'PR] }
    let w : (R ⊗[K] Matrix κ κ D)ˣ :=
      Units.map (matrixChartR (n := κ) e R).symm.toMonoidHom gu
    have hw : matrixChartR (n := κ) e R (w : R ⊗[K] Matrix κ κ D) = P'R * gm * PR := by
      exact (matrixChartR (n := κ) e R).apply_symm_apply _
    have hwg : conjugatedMatrix e R P P' w = g := by
      rw [conjugatedMatrix, hw]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc PR P'R, hPP'R, Matrix.one_mul, Matrix.mul_one]
    have hwmem : w ∈ σ.isometryUnits Q R := by
      rw [← conjugatedMatrix_mem_iff e σ hσ R P P' Q hP'P hPQ, hwg]
      exact g.2
    exact ⟨⟨w, hwmem⟩, Subtype.ext hwg⟩

include hσ in
/-- The all-coefficient isometry-unit comparison for a supplied hyperbolic basis. -/
def splitUnitsEquiv : σ.isometryUnits Q R ≃* OrthogonalMatrix.orthogonalGroup (Fin n) R :=
  MulEquiv.ofBijective (splitUnitsHom e σ hσ R P P' Q hPP' hP'P hPQ)
    (splitUnitsHom_bijective e σ hσ R P P' Q hPP' hP'P hPQ)

include hσ in
theorem coe_splitUnitsEquiv (y : σ.isometryUnits Q R) :
    (splitUnitsEquiv e σ hσ R P P' Q hPP' hP'P hPQ y :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R) = conjugatedMatrix e R P P' y.1 := rfl

include hσ in
theorem splitUnitsEquiv_naturality {S : Type u} [CommRing S] [Algebra K S] [Algebra L S]
    [IsScalarTower K L S] (φ : R →ₐ[L] S) (y : σ.isometryUnits Q R) :
    splitUnitsEquiv e σ hσ S P P' Q hPP' hP'P hPQ
        (IsometryCut.isometrySubgroupMap σ.isStable_quadraticKernel Q (φ.restrictScalars K) y) =
      OrthogonalMatrix.map (Fin n) φ.toRingHom
        (splitUnitsEquiv e σ hσ R P P' Q hPP' hP'P hPQ y) := by
  apply Subtype.ext
  simp only [coe_splitUnitsEquiv, OrthogonalMatrix.coe_map]
  rw [IsometryCut.coe_isometrySubgroupMap]
  rw [conjugatedMatrix, conjugatedMatrix, matrixChartR_naturality, Matrix.map_mul,
    Matrix.map_mul, Matrix.map_map, Matrix.map_map]
  congr 2 <;> ext <;> simp

end Conjugation
end Langlands.GroupScheme.Quaternionic.OrthogonalMorita
