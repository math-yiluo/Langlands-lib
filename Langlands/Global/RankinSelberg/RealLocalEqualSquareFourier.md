# Real square Schwartz tests and their Fourier factorization

**Source.** Hervé Jacquet, *Archimedean Rankin–Selberg Integrals* (2009), §8.2, pp. 55–56. There the test function on the larger square matrices in (8.1) is the product of a rectangular test on the first `t+1` rows and a row test on the last row, and its Fourier transform is the product of the two partial Fourier transforms. This module is the real, equal-rank, Lean form of that elementary step. It is an internal supporting result.

## Definitions

Write `m = t + 1` and `n = t + 2`, `X` for real `m × n` matrices, `Y` for real `n × n` matrices and `Row` for `Fin n → ℝ`.

- `equalSquareSchwartz Φ φ` packages, for Schwartz functions `Φ : 𝓢(X, ℂ)` and `φ : 𝓢(Row, ℂ)`, the function `A ↦ Φ(first m rows of A) · φ(last row of A)` as a Schwartz function in `𝓢(Y, ℂ)`. The theorem `equalSquareSchwartz_apply` states that its values are exactly `equalSquareTest Φ φ A`, the test function used by `realLocalEqualUnfolding`.
- The private helper `complexSchwartzProduct f g` is the Schwartz function `(x, y) ↦ f x · g y` on a product of two real normed spaces. The private continuous linear equivalence `squareRows` sends a square matrix to the pair (last row, first `m` rows), via `Fin.snocEquiv`.

## Statements

- `equalSquareFourierIntegral b Φ φ B` holds for arbitrary functions `Φ` and `φ`, with no integrability hypothesis. The raw rectangular Fourier integral of `equalSquareTest Φ φ` at `B`, with `realScaledCharacter b` and its self-dual measure `realSelfDualMeasure b`, equals the rectangular Fourier integral of `Φ` at the first `m` rows of `B` times `realFourierTransform b φ` at the last row of `B`.
- `RealLocalEqualSquareFourierStatement t` states that for every nonzero real `b` and Schwartz `Φ`, `φ`, the positive square Fourier transform `realRectangularSchwartzFourier b (equalSquareSchwartz Φ φ)` equals `equalSquareTest (realRectangularSchwartzFourier b Φ) (realFourierTransform b φ)` pointwise. The theorem `realLocalEqualSquareFourier` proves it.

The same parameter `b` occurs in the square, rectangular and row transforms; none of them is negated. This is the shape of the two Fourier tests in `RealLocalEqualDualUnfoldingStatement`. In the convention of `RealLocalUniformPositiveEqualContinuationStatement` one takes `b = -a`.

## Implemented proof

1. *Schwartz product.* The function `(x, y) ↦ f x · g y` is smooth as a product of smooth functions composed with the two projections. For the decay estimate, the Leibniz bound `norm_iteratedFDeriv_mul_le` bounds the `n`-th derivative by a binomial sum. The derivative of `f ∘ fst` of order `i` is bounded by that of `f` at the first coordinate, because composition with a linear map of norm at most `1` does not increase the norm of iterated derivatives (the private lemma `norm_deriv_comp_le`). The same holds for `g ∘ snd`. Since the product norm is the maximum of the two coordinate norms, the weight `‖p‖^k` is placed on whichever coordinate is larger. This gives the explicit bound `∑_{i ≤ n} C(n,i) (S_{k,i}(f) S_{0,n-i}(g) + S_{0,i}(f) S_{k,n-i}(g))` in the Schwartz seminorms. The square test is the composition of this product with the continuous linear equivalence `squareRows`.
2. *Fubini.* The measurable equivalence `MeasurableEquiv.piFinSuccAbove` at the last index splits the product measure on `Y` measure-preservingly as the measure on the last row times the rectangular measure on the first `m` rows (`measurePreserving_piFinSuccAbove`). Splitting the last term from the sum by `Fin.sum_univ_castSucc` gives the pairing of the first `m` rows with those of `B`, plus the dot product of the two last rows. The additive character turns this sum into a product, so the integrand is a product of a function of the last row and a function of the first rows. `integral_prod_mul` then factors the integral; this lemma needs no integrability.
3. *Schwartz form.* `realRectangularSchwartzFourier_apply` identifies each Schwartz Fourier transform with the raw rectangular Fourier integral, so step 2 gives the statement.

## Scope

This pair supplies only the square Schwartz test and the factorization of its Fourier transform. It assumes and proves nothing about Whittaker functions, quotient integrals, integrability, meromorphic continuation or functional equations, and it does not prove `RealLocalUniformPositiveEqualContinuationStatement`.
