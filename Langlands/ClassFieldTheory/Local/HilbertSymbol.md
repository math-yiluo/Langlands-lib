# The quadratic Hilbert symbol of a nonarchimedean local field

**GKT Appendix B.3**: **Proposition B.51** (iv), (v) and **Corollary B.52** (b) (p. 625), which
characterize the quadratic Hilbert symbol `(a, b)_F` used throughout the book (chapter 3,
Proposition 3.19; Definition B.28) through the norms of `F(√a)`.

The module `Langlands.ClassFieldTheory.Local.HilbertSymbol` defines `(a, b)_F` for a
nonarchimedean local field `F` with `2 ≠ 0` from the quadratic character of the extension
`F(√a)`, which the Library has already: `LocalClassField.normResidueSign F E`
(`Langlands/ClassFieldTheory/Local/QuadraticNormIndex.lean`, from local reciprocity in NYLL: the
norms of a quadratic extension have index two).

## Content

- `quadraticAlgebraConj a`: the conjugation `x + y ω ↦ x - y ω` of Mathlib's
  `QuadraticAlgebra F a 0` (`ω² = a`); `isQuadraticInvolution_quadraticAlgebraConj`: for `a ≠ 0`
  it is a quadratic involution (`IsQuadraticInvolution`, `Langlands/Group/Unitary/Basic.lean`), so
  `F[ω]` is Galois over `F` when `2 ≠ 0`; `algebra_norm_quadraticAlgebra`: `N(x + y ω) = x² - a y²`.
- `hilbertSymbol F a : Fˣ →* ℤˣ`, `b ↦ (a, b)_F`: `1` if `a` is a square, and otherwise
  `normResidueSign F (QuadraticAlgebra F a 0)` (Mathlib's instance makes `QuadraticAlgebra F a 0` a
  field for a non-square `a`). This is Proposition B.51 (v) with Corollary B.52 (b) read as a
  definition: `(a, b)_F = 1` exactly when `a` is a square or `b ∈ N_{E/F}(Eˣ)`, `E = F(√a)`.
- `hilbertSymbol_eq_one_iff`: `(a, b)_F = 1 ↔ ∃ x y, x² - a y² = b`
  (`exists_sq_sub_mul_sq_of_isSquare`: for a square `a` the form `x² - a y²` represents everything);
  `hilbertSymbol_eq_one_or`, `hilbertSymbol_eq_neg_one_iff`, `hilbertSymbol_mul_self`.
- `hilbertSymbol_eq_one_iff_exists_conic` (Proposition B.51 (iv)): `(a, b)_F = 1` if and only if
  `z² = a x² + b y²` has a solution `(x, y, z) ≠ 0`. The book asks for a solution with `z ≠ 0`;
  over an infinite field the two conditions are equivalent (an isotropic ternary form has
  infinitely many zeros, at most two of them on `z = 0`).
- `hilbertSymbol_comm`: `(a, b)_F = (b, a)_F` (the conic criterion is symmetric);
  `hilbertSymbol_mul_left` with `map_mul`: bimultiplicativity; `hilbertSymbol_prod_left`:
  `(∏ aᵢ, b)_F = ∏ (aᵢ, b)_F`.
- `hilbertSymbol_one_left`, `hilbertSymbol_sq_right`, `hilbertSymbol_sq_left`,
  `hilbertSymbol_mul_sq_right`, `hilbertSymbol_mul_sq_left`: `(a, ·)` depends on `a` modulo squares;
  `hilbertSymbol_inv_left`, `hilbertSymbol_inv_right`: `(a⁻¹, b) = (a, b) = (a, b⁻¹)`;
  `hilbertSymbol_neg_self`: `(a, -a) = 1`; `hilbertSymbol_one_sub`: `(a, 1 - a) = 1`;
  `hilbertSymbol_self`: `(a, a) = (a, -1)`.
- `exists_hilbertSymbol_eq_neg_one`: non-degeneracy: for a non-square `a` there is `b` with
  `(a, b)_F = -1` (`index_range_norm_eq_two`).
- `normResidueSign_eq_hilbertSymbol`, `normSign_eq_hilbertSymbol`: for any quadratic extension
  `E = F(δ)` with a quadratic involution `c` (`c δ = -δ`) and `δ² = d`, the quadratic character
  `η_{E/F}` is `(d, ·)_F` (both are `1` exactly on the values of `x² - d y²`).

The book states B.51 and B.52 without proof ("Everything in this section can be found in virtually
any textbook", p. 623) and uses the Hilbert symbol without defining it; the properties above are
the ones it calls "well-known properties of Hilbert symbol" in the proof of Corollary 3.20 (p. 85).
The real and complex cases are described in
[Archimedean Hilbert symbols](../../KTheory/ArchimedeanHilbertSymbol.md).

## Literature

W. T. Gan, S. S. Kudla, S. Takeda, *The Local Theta Correspondence* (book draft, 2025), Appendix
B.3: Definition B.40, p. 623; Proposition B.51 and Corollary B.52, p. 625; Corollary 3.20, p. 85.

## Declarations

- `Langlands.LocalClassField.quadraticAlgebraConj`, `quadraticAlgebraConj_apply`,
  `isQuadraticInvolution_quadraticAlgebraConj`, `algebra_norm_quadraticAlgebra`.
- `hilbertSymbol`, `exists_sq_sub_mul_sq_of_isSquare`, `hilbertSymbol_eq_one_iff`,
  `hilbertSymbol_eq_one_or`, `hilbertSymbol_mul_self`, `hilbertSymbol_eq_neg_one_iff`,
  `hilbertSymbol_eq_one_iff_exists_conic`, `hilbertSymbol_comm`, `hilbertSymbol_mul_left`,
  `hilbertSymbol_prod_left`,
  `hilbertSymbol_one_left`, `hilbertSymbol_sq_right`, `hilbertSymbol_sq_left`,
  `hilbertSymbol_mul_sq_right`, `hilbertSymbol_mul_sq_left`, `hilbertSymbol_inv_left`,
  `hilbertSymbol_inv_right`, `hilbertSymbol_neg_self`,
  `hilbertSymbol_one_sub`, `hilbertSymbol_self`, `exists_hilbertSymbol_eq_neg_one`.
- `normResidueSign_eq_hilbertSymbol`, `normSign_eq_hilbertSymbol`.

## Dependencies

`Langlands.ClassFieldTheory.Local.QuadraticNormBall` (and through it `QuadraticNormIndex`),
`Langlands.Group.Unitary.Basic`; Mathlib: `Algebra.QuadraticAlgebra.NormDeterminant`,
`Algebra.QuadraticAlgebra.IsQuadraticExtension`.
