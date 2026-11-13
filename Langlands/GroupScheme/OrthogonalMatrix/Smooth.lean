import Langlands.GroupScheme.OrthogonalMatrix.Basic
import Langlands.GroupScheme.SymplecticMatrix.Smooth

/-! # Smoothness of the split orthogonal group scheme

An orthogonal matrix `x` over a square-zero quotient `C ⧸ N` lifts to an orthogonal matrix over
`C`. Write `defect x = U' - U'ᵀ`, choose entrywise lifts `g` of `x` and `U` of `U'`, and put
`ε = defect g - (U - Uᵀ)`, a matrix with entries in `N`. Then `(1 - ε J) g` is orthogonal: its
defect is `W - Wᵀ` for `W = U + ε P + E U + U Eᵀ`, where `E = -ε J` and `P = Q J`. Hence the
coordinate ring of `OrthogonalMatrix.groupScheme l R` is formally smooth; it is of finite
presentation, so the group scheme is smooth over `Spec R`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MvPolynomial
open scoped Matrix

namespace Langlands.GroupScheme.OrthogonalMatrix

open SymplecticMatrix (IsSmall isSmall_of_map_eq_zero)

section Lifting

variable {l : Type} [Fintype l] [DecidableEq l] {C : Type*} [CommRing C]

/-- The projection `P = Q J = [[1, 0], [0, 0]]` onto the first block. -/
def firstProjection : Matrix (l ⊕ l) (l ⊕ l) C :=
  Matrix.fromBlocks 1 0 0 0

omit [Fintype l] in
theorem firstProjection_transpose : (firstProjection : Matrix (l ⊕ l) (l ⊕ l) C)ᵀ =
    firstProjection := by
  simp [firstProjection, Matrix.fromBlocks_transpose]

theorem formMatrix_mul_polarMatrix :
    formMatrix l C * polarMatrix l C = firstProjection := by
  simp [formMatrix, polarMatrix, firstProjection, Matrix.fromBlocks_multiply]

theorem polarMatrix_mul_formMatrix :
    polarMatrix l C * formMatrix l C = 1 - firstProjection := by
  simp only [formMatrix, polarMatrix, firstProjection, Matrix.fromBlocks_multiply]
  rw [eq_sub_iff_add_eq, Matrix.fromBlocks_add, ← Matrix.fromBlocks_one]
  simp

variable {N : Ideal C}

omit [Fintype l] [DecidableEq l] in
theorem isSmall_neg {A : Matrix (l ⊕ l) (l ⊕ l) C} (hA : IsSmall N A) : IsSmall N (-A) :=
  fun i j => by simpa using N.neg_mem (hA i j)

/-- **Correction of an approximately orthogonal matrix.** If `ε = defect g - (U - Uᵀ)` has
entries in a square-zero ideal, then `(1 - ε J) g` is orthogonal. -/
theorem correction_mem (hN : N ^ 2 = ⊥) (g U : Matrix (l ⊕ l) (l ⊕ l) C)
    (hε : IsSmall N (defect g - (U - Uᵀ))) :
    (1 - (defect g - (U - Uᵀ)) * polarMatrix l C) * g ∈ orthogonalGroup l C := by
  set Q := formMatrix l C with hQdef
  set J := polarMatrix l C with hJdef
  set P : Matrix (l ⊕ l) (l ⊕ l) C := firstProjection with hPdef
  set ε := defect g - (U - Uᵀ) with hεdef
  set A := U - Uᵀ with hAdef
  set E := -(ε * J) with hEdef
  have hE : IsSmall N E := isSmall_neg (hε.mul_right J)
  have hET : IsSmall N Eᵀ := hE.transpose
  have hEε : E * ε = 0 := hE.mul_eq_zero hN hε
  have hεE : ε * Eᵀ = 0 := hε.mul_eq_zero hN hET
  have hEQE : E * (Q * Eᵀ) = 0 := hE.mul_eq_zero hN (hET.mul_left Q)
  have hEAE : E * (A * Eᵀ) = 0 := hE.mul_eq_zero hN (hET.mul_left A)
  have hEQ : E * Q = -ε + ε * P := by
    rw [hEdef, Matrix.neg_mul, Matrix.mul_assoc, hJdef, hQdef, polarMatrix_mul_formMatrix,
      Matrix.mul_sub, Matrix.mul_one]
    abel
  have hQE : Q * Eᵀ = -(P * εᵀ) := by
    rw [hEdef, Matrix.transpose_neg, Matrix.transpose_mul, hJdef, polarMatrix_transpose,
      Matrix.mul_neg, ← Matrix.mul_assoc, hQdef, formMatrix_mul_polarMatrix]
  have hgQg : g * Q * gᵀ = Q + A + ε := by
    rw [hεdef, defect]
    abel
  have hsub : (1 - ε * J) = 1 + E := by rw [hEdef, sub_eq_add_neg]
  rw [hsub, mem_orthogonalGroup_iff]
  refine ⟨U + ε * P + E * U + U * Eᵀ, ?_⟩
  calc defect ((1 + E) * g) = (1 + E) * (g * Q * gᵀ) * (1 + Eᵀ) - Q := by
        rw [defect, ← hQdef, Matrix.transpose_mul, Matrix.transpose_add, Matrix.transpose_one]
        simp only [Matrix.mul_assoc]
    _ = (1 + E) * (Q + A + ε) * (1 + Eᵀ) - Q := by rw [hgQg]
    _ = A + ε + E * Q + Q * Eᵀ + E * A + A * Eᵀ +
          (E * ε + ε * Eᵀ + E * (Q * Eᵀ) + E * (A * Eᵀ) + E * (ε * Eᵀ)) := by
        simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
          Matrix.mul_assoc]
        abel
    _ = A + ε + E * Q + Q * Eᵀ + E * A + A * Eᵀ := by
        rw [hEε, hεE, hEQE, hEAE]
        simp
    _ = U + ε * P + E * U + U * Eᵀ - (U + ε * P + E * U + U * Eᵀ)ᵀ := by
        rw [hEQ, hQE]
        simp only [hAdef, Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_transpose,
          hPdef, firstProjection_transpose, Matrix.mul_sub, Matrix.sub_mul]
        abel

/-- **Infinitesimal lifting.** Every orthogonal matrix over a square-zero quotient `C ⧸ N` lifts
to an orthogonal matrix over `C`. -/
theorem exists_map_eq (hN : N ^ 2 = ⊥) (x : orthogonalGroup l (C ⧸ N)) :
    ∃ y : orthogonalGroup l C, map l (Ideal.Quotient.mk N) y = x := by
  obtain ⟨U', hU'⟩ := (mem_orthogonalGroup_iff _).1 x.2
  let lift : Matrix (l ⊕ l) (l ⊕ l) (C ⧸ N) → Matrix (l ⊕ l) (l ⊕ l) C := fun M =>
    Matrix.of fun i j => Function.surjInv Ideal.Quotient.mk_surjective (M i j)
  have hlift : ∀ M, (lift M).map (Ideal.Quotient.mk N) = M := fun M => by
    ext i j
    exact Function.surjInv_eq Ideal.Quotient.mk_surjective _
  have hε : IsSmall N (defect (lift x) - (lift U' - (lift U')ᵀ)) := by
    apply isSmall_of_map_eq_zero
    rw [Matrix.map_sub _ (map_sub _), Matrix.map_sub _ (map_sub _), defect_map,
      Matrix.transpose_map, hlift, hlift, hU', sub_self]
  refine ⟨⟨_, correction_mem hN (lift x) (lift U') hε⟩, Subtype.ext ?_⟩
  have hsmall : IsSmall N ((defect (lift x) - (lift U' - (lift U')ᵀ)) * polarMatrix l C) :=
    hε.mul_right _
  change ((1 - _) * lift x).map (Ideal.Quotient.mk N) = _
  rw [← RingHom.mapMatrix_apply, map_mul, map_sub, map_one, RingHom.mapMatrix_apply,
    hsmall.map_eq_zero, sub_zero, one_mul, RingHom.mapMatrix_apply, hlift]

end Lifting

section Algebra

variable (l : Type) [Fintype l] [DecidableEq l] (R : Type u) [CommRing R]

/-- The defining ideal is finitely generated. -/
theorem ideal_fg : (ideal l R).FG :=
  Submodule.fg_span ((Set.finite_range _).union (Set.finite_range _))

instance finitePresentation_coordinateRing :
    Algebra.FinitePresentation R (CoordinateRing l R) :=
  Algebra.FinitePresentation.quotient (ideal_fg l R)

instance formallySmooth_coordinateRing : Algebra.FormallySmooth R (CoordinateRing l R) := by
  refine Algebra.FormallySmooth.of_comp_surjective fun C _ _ N hN f => ?_
  obtain ⟨y, hy⟩ := exists_map_eq hN (point f)
  refine ⟨classify y, ?_⟩
  rw [← classify_map]
  change classify (map l (Ideal.Quotient.mk N) y) = f
  rw [hy, classify_point]

instance smooth_coordinateRing : Algebra.Smooth R (CoordinateRing l R) where

end Algebra

/-- **Smoothness.** The split orthogonal group scheme is smooth over its base. -/
instance smooth_groupScheme (l : Type) [Fintype l] [DecidableEq l] (R : CommRingCat.{u}) :
    Smooth (groupScheme l R).X.hom :=
  Corepresented.smooth_groupScheme_iff.mpr
    (inferInstanceAs (Algebra.Smooth R (CoordinateRing l R)))

end Langlands.GroupScheme.OrthogonalMatrix
