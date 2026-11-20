import Langlands.GroupScheme.SymplecticMatrix.Darboux
import Langlands.LinearAlgebra.GeneralLinearGaloisFixedBasis
import Mathlib.FieldTheory.Galois.Basic

/-! # Galois coboundaries in split symplectic matrices -/

noncomputable section

open Matrix

universe u

namespace Langlands.GroupScheme.SymplecticMatrix

variable {K L : Type u} [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L] {n : ℕ}

local notation "I" => Fin n ⊕ Fin n

private theorem sandwich_mul {R : Type*} [CommRing R] {ι : Type*} [Fintype ι]
    (a b c : Matrix ι ι R) : (a * b) * c * (a * b)ᵀ = a * (b * c * bᵀ) * aᵀ := by
  rw [Matrix.transpose_mul]
  simp only [Matrix.mul_assoc]

private theorem J_diag {R : Type*} [CommRing R] (i : I) : J (Fin n) R i i = 0 := by
  cases i <;> rfl

/-- Matrix Hilbert 90 for the split symplectic group. -/
theorem exists_symplectic_coboundary (c : (L ≃ₐ[K] L) → GL I L)
    (hc : ∀ σ τ, c (σ * τ) = c σ * GeneralLinearGroup.map σ.toRingHom (c τ))
    (hJ : ∀ σ, (c σ : Matrix I I L) ∈ Matrix.symplecticGroup (Fin n) L) :
    ∃ b : GL I L, (b : Matrix I I L) ∈ Matrix.symplecticGroup (Fin n) L ∧
      ∀ σ, c σ * GeneralLinearGroup.map σ.toRingHom b = b := by
  classical
  obtain ⟨b, hb⟩ := Langlands.LinearAlgebra.GaloisFixedBasis.exists_fixed (g := c) hc
  let v := b⁻¹
  let D := (v : Matrix I I L) * J (Fin n) L * (v : Matrix I I L)ᵀ
  have hv (σ : L ≃ₐ[K] L) : GeneralLinearGroup.map σ.toRingHom v = v * c σ := by
    have h := congrArg Inv.inv (hb σ)
    rw [_root_.mul_inv_rev, ← map_inv] at h
    exact mul_inv_eq_iff_eq_mul.mp h
  have hfix (σ : L ≃ₐ[K] L) : D.map σ = D := by
    have h := congrArg Units.val (hv σ)
    change (v : Matrix I I L).map σ = (v : Matrix I I L) * (c σ : Matrix I I L) at h
    rw [show D.map σ = (v : Matrix I I L).map σ * J (Fin n) L *
        ((v : Matrix I I L).map σ)ᵀ by simp only [D, Matrix.map_mul, Matrix.map_J, Matrix.transpose_map],
      h, sandwich_mul, SymplecticGroup.mem_iff.mp (hJ σ)]
  choose d hd using fun (i j : I) =>
    (IsGalois.mem_range_algebraMap_iff_fixed (F := K) (D i j)).mpr
      (fun σ => congrArg (fun M : Matrix I I L => M i j) (hfix σ))
  let C : Matrix I I K := Matrix.of d
  have hC : C.map (algebraMap K L) = D := Matrix.ext hd
  have htranspose : Cᵀ = -C := by
    have hh : Dᵀ = -D := by
      simp only [D, Matrix.transpose_mul, transpose_transpose, Matrix.J_transpose,
        Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc]
    ext i j
    apply (algebraMap K L).injective
    change algebraMap K L (d j i) = algebraMap K L (-d i j)
    simpa only [Matrix.transpose_apply, Matrix.neg_apply, map_neg, hd] using
      congrArg (fun M : Matrix I I L => M i j) hh
  have hdiag (i : I) : C i i = 0 := by
    apply (algebraMap K L).injective
    have hh := dotProduct_mulVec_self_eq_zero (J_transpose (Fin n) L) J_diag
      (fun j => (v : Matrix I I L) i j)
    change algebraMap K L (d i i) = algebraMap K L 0
    rw [hd, map_zero]
    simpa only [D, Matrix.mul_assoc, Matrix.mul_apply, Matrix.transpose_apply,
      dotProduct, Matrix.mulVec] using hh
  have hdet : C.det ≠ 0 := by
    have hvd := ((Matrix.isUnit_iff_isUnit_det _).mp v.isUnit).ne_zero
    have hD : D.det ≠ 0 := by
      change ((v : Matrix I I L) * J (Fin n) L * (v : Matrix I I L)ᵀ).det ≠ 0
      rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
      exact mul_ne_zero (mul_ne_zero hvd (Matrix.isUnit_det_J (Fin n) L).ne_zero) hvd
    intro hz
    apply hD
    rw [← hC]
    change ((algebraMap K L).mapMatrix C).det = 0
    rw [← RingHom.map_det, hz, map_zero]
  obtain ⟨m, P, Q, hPQ, hQP, hP⟩ := exists_mul_mul_transpose_eq_J C htranspose hdiag hdet
  have hmn : m = n := by
    have hp := (Matrix.rank_mul_le_left P Q).trans P.rank_le_card_width
    have hq := (Matrix.rank_mul_le_left Q P).trans Q.rank_le_card_width
    simp only [hPQ, hQP, Matrix.rank_one, Fintype.card_sum, Fintype.card_fin] at hp hq
    omega
  subst m
  let q : GL I K := ⟨Q, P, hQP, hPQ⟩
  have hq : Q * J (Fin n) K * Qᵀ = C := by
    rw [← hP, ← sandwich_mul, hQP, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]
  let qL := GeneralLinearGroup.map (algebraMap K L) q
  have hqL : (qL : Matrix I I L) * J (Fin n) L * (qL : Matrix I I L)ᵀ = D := by
    change Q.map (algebraMap K L) * J (Fin n) L * (Q.map (algebraMap K L))ᵀ = D
    simpa only [Matrix.map_mul, Matrix.map_J, Matrix.transpose_map, hC] using
      congrArg (fun M : Matrix I I K => M.map (algebraMap K L)) hq
  refine ⟨b * qL, SymplecticGroup.mem_iff.mpr ?_, fun σ => ?_⟩
  · change ((b : Matrix I I L) * (qL : Matrix I I L)) * J (Fin n) L *
      ((b : Matrix I I L) * (qL : Matrix I I L))ᵀ = J (Fin n) L
    rw [sandwich_mul, hqL, ← sandwich_mul]
    rw [show (b : Matrix I I L) * (v : Matrix I I L) = 1 from b.mul_inv,
      Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]
  · have hqfix : GeneralLinearGroup.map σ.toRingHom qL = qL := by
      apply Units.ext
      ext i j
      exact σ.commutes (Q i j)
    rw [map_mul, hqfix, ← mul_assoc]
    exact congrArg (fun x => x * qL) (hb σ)

/-- Triviality of the matrix cocycle kernel for the split symplectic group. -/
def SplitSymplecticGaloisCoboundaryStatement : Prop :=
  ∀ (K L : Type u) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
      (n : ℕ) (c : (L ≃ₐ[K] L) → GL (Fin n ⊕ Fin n) L),
    (∀ σ τ, c (σ * τ) = c σ * GeneralLinearGroup.map σ.toRingHom (c τ)) →
    (∀ σ, (c σ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) L) ∈ Matrix.symplecticGroup (Fin n) L) →
    ∃ b : GL (Fin n ⊕ Fin n) L,
      (b : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) L) ∈ Matrix.symplecticGroup (Fin n) L ∧
      ∀ σ, c σ * GeneralLinearGroup.map σ.toRingHom b = b

/-- Every split symplectic matrix cocycle is a coboundary. -/
theorem splitSymplecticGaloisCoboundary : SplitSymplecticGaloisCoboundaryStatement.{u} := by
  intro K L _ _ _ _ _ n c hc hJ
  exact exists_symplectic_coboundary c hc hJ

end Langlands.GroupScheme.SymplecticMatrix
