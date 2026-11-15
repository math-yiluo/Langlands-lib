import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Analysis.Complex.Basic

/-!
# Coordinates on a finite product of matrix algebras

For `n : ι → ℕ` the product `∏ᵢ 𝔤𝔩_{n i}` has the coordinates `X ⟨i, p, q⟩`,
`(i, p, q) ∈ Coord n = Σ i, Fin (n i) × Fin (n i)`. `blockMatrix K n i` is the generic matrix
of block `i` over the polynomial ring `K[X_c]`, and `genericBlock n i` is the case `K = ℂ`.
-/

noncomputable section

set_option autoImplicit false

namespace Langlands.Archimedean.Kostant

open MvPolynomial

variable {ι : Type*} (n : ι → ℕ)

/-- Index type of the matrix coordinates of `∏ᵢ 𝔤𝔩_{n i}`. -/
abbrev Coord := Σ i, Fin (n i) × Fin (n i)

/-- The generic matrix of block `i` over `K[X_c]`. -/
def blockMatrix (K : Type*) [CommRing K] (i : ι) :
    Matrix (Fin (n i)) (Fin (n i)) (MvPolynomial (Coord n) K) :=
  Matrix.of fun p q => X ⟨i, p, q⟩

/-- The generic matrix of block `i` over `ℂ[X_c]`. -/
def genericBlock (i : ι) : Matrix (Fin (n i)) (Fin (n i)) (MvPolynomial (Coord n) ℂ) :=
  Matrix.of fun p q => X ⟨i, p, q⟩

theorem blockMatrix_complex (i : ι) : blockMatrix n ℂ i = genericBlock n i := rfl

end Langlands.Archimedean.Kostant
