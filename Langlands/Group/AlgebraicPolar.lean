import Langlands.Group.AlgebraicMatrixPowers
import Mathlib.Analysis.Matrix.PosDef

/-! # Positive powers and square roots in algebraic matrix subgroups -/

noncomputable section

universe u v

namespace Langlands.Group.AlgebraicPolar

open Matrix
open Langlands.Group.AlgebraicMatrixPowers
open Langlands.Group.PositivePowerPolynomial
open scoped ComplexOrder

variable {𝕜 : Type u} [RCLike 𝕜] {n : Type} [Fintype n] [DecidableEq n]

/-- Positive real powers defined using the Hermitian spectral basis. -/
def positivePower (g : GL n 𝕜) (hg : g.val.PosDef) (r : ℝ) : GL n 𝕜 :=
  conjugatedPower (Unitary.toUnits hg.isHermitian.eigenvectorUnitary)
    hg.isHermitian.eigenvalues hg.eigenvalues_pos r

@[simp] theorem positivePower_one (g : GL n 𝕜) (hg : g.val.PosDef) :
    positivePower g hg 1 = g := by
  apply Units.ext
  change (hg.isHermitian.eigenvectorUnitary : Matrix n n 𝕜) *
      diagonal (fun i => (RCLike.ofReal (hg.isHermitian.eigenvalues i ^ (1 : ℝ)) : 𝕜)) *
      star (hg.isHermitian.eigenvectorUnitary : Matrix n n 𝕜) = g.val
  simpa only [Unitary.conjStarAlgAut_apply, Real.rpow_one,
    Function.comp_def] using hg.isHermitian.spectral_theorem.symm

/-- The constructed powers are positive definite for every real exponent. -/
theorem positivePower_posDef (g : GL n 𝕜) (hg : g.val.PosDef) (r : ℝ) :
    (positivePower g hg r).val.PosDef := by
  change ((hg.isHermitian.eigenvectorUnitary : Matrix n n 𝕜) *
      diagonal (powerPoint hg.isHermitian.eigenvalues r) *
      star (hg.isHermitian.eigenvectorUnitary : Matrix n n 𝕜)).PosDef
  apply Unitary.isUnit_coe.posDef_star_right_conjugate_iff.mpr
  apply Matrix.posDef_diagonal_iff.mpr
  intro i
  exact RCLike.ofReal_pos.mpr (Real.rpow_pos_of_pos (hg.eigenvalues_pos i) r)

private theorem diagonalPower_add (x : n → ℝ) (hx : ∀ i, 0 < x i) (r s : ℝ) :
    diagonalPower (𝕜 := 𝕜) x hx (r + s) =
      diagonalPower x hx r * diagonalPower x hx s := by
  apply Units.ext
  change diagonal (powerPoint x (r + s)) =
    diagonal (powerPoint (𝕜 := 𝕜) x r) * diagonal (powerPoint x s)
  rw [diagonal_mul_diagonal]
  congr 1
  funext i
  exact (congrArg (RCLike.ofReal : ℝ → 𝕜) (Real.rpow_add (hx i) r s)).trans
    (RCLike.ofReal_mul _ _)

/-- Addition of exponents is multiplication of the constructed positive powers. -/
theorem positivePower_add (g : GL n 𝕜) (hg : g.val.PosDef) (r s : ℝ) :
    positivePower g hg (r + s) = positivePower g hg r * positivePower g hg s := by
  unfold positivePower conjugatedPower
  rw [diagonalPower_add, map_mul]

/-- The spectral power with exponent one half squares to the original matrix unit. -/
theorem positivePower_half_sq (g : GL n 𝕜) (hg : g.val.PosDef) :
    positivePower g hg (1 / 2) * positivePower g hg (1 / 2) = g := by
  rw [← positivePower_add]
  norm_num

/-- Positive powers remain inside any polynomially defined subgroup. -/
theorem positivePower_mem (H : Subgroup (GL n 𝕜)) (hH : IsPolynomiallyDefined H)
    (g : GL n 𝕜) (hg : g.val.PosDef) (hmem : g ∈ H) (r : ℝ) :
    positivePower g hg r ∈ H := by
  apply conjugatedPower_mem H hH
  change positivePower g hg 1 ∈ H
  simpa only [positivePower_one] using hmem

/-- Every positive definite element of a polynomially defined subgroup has an
internal positive definite square root. -/
theorem exists_positive_sqrt (H : Subgroup (GL n 𝕜)) (hH : IsPolynomiallyDefined H)
    (g : GL n 𝕜) (hg : g.val.PosDef) (hmem : g ∈ H) :
    ∃ a : GL n 𝕜, a ∈ H ∧ a.val.PosDef ∧ a * a = g :=
  ⟨positivePower g hg (1 / 2), positivePower_mem H hH g hg hmem _,
    positivePower_posDef g hg _, positivePower_half_sq g hg⟩

end Langlands.Group.AlgebraicPolar
