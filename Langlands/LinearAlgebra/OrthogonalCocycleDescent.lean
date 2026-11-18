import Langlands.LinearAlgebra.GaloisVectorDescent
import Mathlib.FieldTheory.Galois.Basic

/-! # Quadratic forms descended from orthogonal matrix cocycles -/

noncomputable section

universe u w

namespace Langlands.LinearAlgebra.OrthogonalCocycleDescent

open Matrix

variable {k L : Type u} [Field k] [Field L] [Algebra k L]
  {n : Type w} [Fintype n] [DecidableEq n]

/-- A matrix-valued finite-Galois cocycle preserving the scalar extension of a Gram matrix. -/
structure OrthogonalCocycle (H : Matrix n n k) where
  toFun : (L ≃ₐ[k] L) → GL n L
  one : toFun 1 = 1
  mul : ∀ σ τ, toFun (σ * τ) = toFun σ * GeneralLinearGroup.map σ.toRingHom (toFun τ)
  preserves : ∀ σ, (toFun σ : Matrix n n L) * H.map (algebraMap k L) *
    (toFun σ : Matrix n n L)ᵀ = H.map (algebraMap k L)

/-- A ground-field symmetric invertible Gram matrix and an explicit matrix trivializing
the cocycle and identifying its scalar extension with the original Gram matrix. -/
structure Descent {H : Matrix n n k} (c : OrthogonalCocycle (L := L) H) where
  gram : Matrix n n k
  symmetric : gramᵀ = gram
  unit : IsUnit gram
  matrix : GL n L
  coboundary : ∀ σ, c.toFun σ = matrix * GeneralLinearGroup.map σ.toRingHom matrix⁻¹
  gram_eq : gram.map (algebraMap k L) =
    ((matrix⁻¹ : GL n L) : Matrix n n L) * H.map (algebraMap k L) *
      (((matrix⁻¹ : GL n L) : Matrix n n L)ᵀ)

variable [FiniteDimensional k L] [IsGalois k L]

omit [Fintype n] [DecidableEq n] in
/-- A matrix fixed entrywise by the full Galois group has all its entries in the ground field. -/
theorem exists_matrix_of_fixed (A : Matrix n n L)
    (hA : ∀ σ : L ≃ₐ[k] L, A.map σ = A) :
    ∃ B : Matrix n n k, B.map (algebraMap k L) = A := by
  have hcoeff : ∀ i j, ∃ a : k, algebraMap k L a = A i j := by
    intro i j
    apply IntermediateField.mem_bot.mp
    apply (IsGalois.mem_bot_iff_fixed _).mpr
    intro σ
    exact congrArg (fun M : Matrix n n L => M i j) (hA σ)
  choose B hB using hcoeff
  exact ⟨B, Matrix.ext hB⟩

variable {H : Matrix n n k} (c : OrthogonalCocycle (L := L) H)

/-- Orthogonal matrix cocycles descend a nondegenerate symmetric form over the ground field. -/
theorem nonempty_descent (hH : Hᵀ = H) (hunit : IsUnit H) :
    Nonempty (Descent c) := by
  let Γ : Subgroup (L ≃ₐ[k] L) := ⊤
  obtain ⟨P, hP⟩ := GaloisVectorDescent.exists_matrix_coboundary' Γ
    (fun σ => (c.toFun σ.val : Matrix n n L))
    (by simpa using congrArg (fun A : GL n L => (A : Matrix n n L)) c.one)
    (fun σ τ => congrArg (fun A : GL n L => (A : Matrix n n L)) (c.mul σ.val τ.val))
  have hPc (σ : L ≃ₐ[k] L) :
      c.toFun σ = P * GeneralLinearGroup.map σ.toRingHom P⁻¹ :=
    Units.ext (hP ⟨σ, Subgroup.mem_top σ⟩)
  have hinv (σ : L ≃ₐ[k] L) :
      (((P⁻¹ : GL n L) : Matrix n n L)).map σ =
        ((P⁻¹ : GL n L) : Matrix n n L) * (c.toFun σ : Matrix n n L) := by
    rw [hPc]
    change _ = ((P⁻¹ : GL n L) : Matrix n n L) *
      ((P : Matrix n n L) * (((P⁻¹ : GL n L) : Matrix n n L).map σ))
    rw [← mul_assoc, Units.inv_mul, one_mul]
  let A : Matrix n n L :=
    ((P⁻¹ : GL n L) : Matrix n n L) * H.map (algebraMap k L) *
      (((P⁻¹ : GL n L) : Matrix n n L)ᵀ)
  have hfix (σ : L ≃ₐ[k] L) : A.map σ = A := by
    have hbase : (H.map (algebraMap k L)).map σ = H.map (algebraMap k L) := by
      ext i j
      exact σ.commutes (H i j)
    dsimp only [A]
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, hinv, hbase, transpose_mul]
    calc
      _ = ((P⁻¹ : GL n L) : Matrix n n L) *
          ((c.toFun σ : Matrix n n L) * H.map (algebraMap k L) *
            (c.toFun σ : Matrix n n L)ᵀ) *
          (((P⁻¹ : GL n L) : Matrix n n L)ᵀ) := by simp only [mul_assoc]
      _ = _ := by rw [c.preserves]
  obtain ⟨B, hB⟩ := exists_matrix_of_fixed A hfix
  have hsymA : Aᵀ = A := by
    have hs : (H.map (algebraMap k L))ᵀ = H.map (algebraMap k L) := by
      rw [← Matrix.transpose_map, hH]
    simp only [A, transpose_mul, transpose_transpose, hs, mul_assoc]
  have hsymB : Bᵀ = B := by
    apply Matrix.map_injective (algebraMap k L).injective
    change (Bᵀ).map (algebraMap k L) = B.map (algebraMap k L)
    rw [Matrix.transpose_map, hB, hsymA]
  have hunitA : IsUnit A :=
    (((P⁻¹ : GL n L).isUnit).mul (hunit.map (RingHom.mapMatrix (algebraMap k L)))).mul
      ((Matrix.isUnit_transpose _).mpr (P⁻¹ : GL n L).isUnit)
  have hunitB : IsUnit B := by
    apply (Matrix.isUnit_iff_isUnit_det B).mpr
    apply isUnit_iff_ne_zero.mpr
    intro hz
    have hdet : A.det = 0 := by
      rw [← hB]
      change ((algebraMap k L).mapMatrix B).det = 0
      rw [← (algebraMap k L).map_det, hz, map_zero]
    exact (isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det A).mp hunitA)) hdet
  exact ⟨⟨B, hsymB, hunitB, P, hPc, hB⟩⟩

/-- A chosen descended Gram matrix, with its full comparison to the original cocycle. -/
def descent (hH : Hᵀ = H) (hunit : IsUnit H) : Descent c :=
  Classical.choice (nonempty_descent c hH hunit)

end Langlands.LinearAlgebra.OrthogonalCocycleDescent
