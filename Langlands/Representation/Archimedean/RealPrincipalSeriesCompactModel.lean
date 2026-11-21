import Langlands.Representation.Archimedean.PrincipalSeriesExtension
import Langlands.Representation.Archimedean.RealBlockFourierPropagation
import Langlands.Representation.Archimedean.RealPrincipalSeriesCompactAverages

/-! # The continuous compact factor and weight for the real principal series -/

noncomputable section

open scoped Matrix Matrix.Norms.Operator ContDiff

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean.RealPrincipalSeriesHilbert

open RealJacquetFrobenius RealPrincipalSeriesDuality PrincipalSeriesExtension GramFormula

variable {n : ℕ}

local notation "GL" => Langlands.GeneralLinear n ℝ
local notation "Mat" => Matrix (Fin n) (Fin n) ℝ
local notation "O" => Matrix.unitaryGroup (Fin n) ℝ
local notation "K" => unitaryCompact ℝ n

private theorem continuous_signedOrthogonalPart : Continuous (@signedOrthogonalPart n) := by
  apply continuous_induced_rng.mpr
  change Continuous (fun g : GL => signedOrthogonal (g : Mat))
  apply continuous_matrix
  intro i j
  have hG (l : ℕ) : Continuous (fun g : GL => (Real.sqrt (gram l (g : Mat)))⁻¹) := by
    apply (Real.continuous_sqrt.comp ((contDiff_gram l).continuous.comp Units.continuous_val)).inv₀
    intro g
    exact (Real.sqrt_pos.mpr (gram_pos g l)).ne'
  exact (((contDiff_gramColumn i j).continuous.comp Units.continuous_val).mul
    (hG i)).mul (hG ((i : ℕ) + 1))

/-- The orthogonal factor with the signs chosen to make the triangular diagonal positive. -/
def compactFactor : C(GL, K) :=
  ⟨fun g => orthogonalCompactEquiv n (signedOrthogonalPart g),
    continuous_orthogonalCompactEquiv.comp continuous_signedOrthogonalPart⟩

/-- The principal-series scalar weight of the positive-diagonal triangular factor. -/
def compactWeight (a : Fin n → ℂ) : C(GL, ℂ) :=
  ⟨fun g => gramExpression a 1 (complexify (g : Mat)),
    (contDiffOn_gramExpression a 1).continuousOn.comp_continuous Units.continuous_val
      (fun g => g.isUnit)⟩

private theorem compactFactor_of_factorization (g : GL) (b : Mat) (k : K)
    (hb : b.IsUpperTriangular) (hd : ∀ j, b j j ≠ 0)
    (hg : (g : Mat) = b * ((k : GL) : Mat)) :
    compactFactor g = orthogonalCompactEquiv n (signDiagonal fun j => b j j) * k := by
  apply Subtype.ext
  apply Units.ext
  change signedOrthogonal (g : Mat) =
    (Matrix.diagonal fun j => signReal (b j j)) * ((k : GL) : Mat)
  rw [hg, signedOrthogonal_mul hb hd (mul_transpose_eq_one_of_mem k.2)]

private theorem compactWeight_of_factorization (a : Fin n → ℂ) (g : GL) (b : Mat) (k : K)
    (hb : b.IsUpperTriangular) (hd : ∀ j, b j j ≠ 0)
    (hg : (g : Mat) = b * ((k : GL) : Mat)) :
    compactWeight a g = ∏ j : Fin n, ((|b j j| : ℝ) : ℂ) ^ a j := by
  change gramExpression a 1 (complexify (g : Mat)) = _
  rw [hg, gramExpression_complexify_mul hb hd (mul_transpose_eq_one_of_mem k.2)]
  simp

private theorem exists_compactFactorization (g : GL) :
    ∃ (b : Mat) (k : K), b.IsUpperTriangular ∧ (∀ j, b j j ≠ 0) ∧ (g : Mat) = b * ((k : GL) : Mat) := by
  obtain ⟨hb, hbu, -, hg⟩ := iw_spec g
  exact ⟨iwB g, orthogonalCompactEquiv n (iwKU g), hb, fun j => diag_ne_zero hb hbu j, hg⟩

private theorem mul_compact_factorization {g : GL} {b : Mat} {k₀ : K}
    (hg : (g : Mat) = b * ((k₀ : GL) : Mat)) (k : K) :
    ((g * (k : GL) : GL) : Mat) = b * (((k₀ * k : K) : GL) : Mat) := by
  change (g : Mat) * ((k : GL) : Mat) = b * (((k₀ : GL) : Mat) * ((k : GL) : Mat))
  rw [hg, mul_assoc]

/-- The positive-diagonal compact factor is equivariant for right orthogonal translation. -/
theorem compactFactor_mul_compact (g : GL) (k : K) :
    compactFactor (g * (k : GL)) = compactFactor g * k := by
  obtain ⟨b, k₀, hb, hd, hg⟩ := exists_compactFactorization g
  have hm := mul_compact_factorization hg k
  rw [compactFactor_of_factorization _ _ _ hb hd hm, compactFactor_of_factorization _ _ _ hb hd hg, mul_assoc]

/-- The principal-series weight is invariant under right orthogonal translation. -/
theorem compactWeight_mul_compact (a : Fin n → ℂ) (g : GL) (k : K) :
    compactWeight a (g * (k : GL)) = compactWeight a g := by
  obtain ⟨b, k₀, hb, hd, hg⟩ := exists_compactFactorization g
  have hm := mul_compact_factorization hg k
  rw [compactWeight_of_factorization a _ _ _ hb hd hm, compactWeight_of_factorization a _ _ _ hb hd hg]

/-- The original smooth principal-series function is its compact profile extended by the
positive-diagonal weight. -/
theorem principalSeries_eq_compactProfile (a : Fin n → ℂ) (e : Fin n → Fin 2)
    (v : PrincipalSeries a e) (g : GL) :
    v.1 g = compactWeight a g * compactRestriction a e v (compactFactor g) := by
  obtain ⟨l, u, k, hk, rfl⟩ := RealBlockPropagation.exists_expDiagonal_mul_upperUnipotent_mul_unitaryCompact g
  let k' : K := ⟨k, hk⟩
  let d : Fin n → ℝˣ := fun j => Units.mk0 (Real.exp (l j)) (Real.exp_pos _).ne'
  let A : GL := Langlands.GeneralLinear.Iwasawa.diagonalUnits d
  let b : Mat := (A : Mat) * ((u : GL) : Mat)
  have hA : matrixExpUnit n (Matrix.diagonal l) = A := matrixExpUnit_diagonal l
  rw [hA]
  let y := A * ((u : GL) * k)
  have hb : b.IsUpperTriangular := isUpperTriangular_diagonal_mul d u
  have hdiag (j : Fin n) : b j j = Real.exp (l j) := diagonal_mul_apply_self d u j
  have hp (j : Fin n) : 0 < b j j := (hdiag j).symm ▸ Real.exp_pos (l j)
  have hy : (y : Mat) = b * ((k' : GL) : Mat) := (mul_assoc _ _ _).symm
  have hsign : signDiagonal (fun j => b j j) = (1 : O) := by
    apply Subtype.ext
    change (Matrix.diagonal fun j => signReal (b j j)) = 1
    simp only [signReal, hp, ite_true, Matrix.diagonal_one]
  change v.1 y = compactWeight a y * compactRestriction a e v (compactFactor y)
  rw [compactFactor_of_factorization y b k' hb (fun j => (hp j).ne') hy, hsign, map_one, one_mul,
    compactWeight_of_factorization a y b k' hb (fun j => (hp j).ne') hy]
  change v.1 (A * ((u : GL) * k)) = (∏ j : Fin n, ((|b j j| : ℝ) : ℂ) ^ a j) * v.1 k
  rw [← mul_assoc, v.2.2 d u k]
  congr 1
  rw [RealJacquetFrobenius.principalSeriesCharacter_eq]
  unfold diagChar
  exact Finset.prod_congr rfl (fun j _ => by
    rw [Matrix.diagonal_apply_eq, charFun, hdiag]
    dsimp only [d, Units.val_mk0]
    rw [abs_of_pos (Real.exp_pos _), div_self (Real.exp_pos _).ne', Complex.ofReal_one,
      one_pow, one_mul])

end Langlands.Archimedean.RealPrincipalSeriesHilbert
