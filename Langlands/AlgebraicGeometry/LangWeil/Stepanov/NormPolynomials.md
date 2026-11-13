# Proof of `StepanovNormPolynomialsStatement`

Author: Worker 5406. The theorem `stepanovNormPolynomials` proves the Library statement
`Langlands.AlgebraicGeometry.LangWeil.StepanovNormPolynomialsStatement` with no hypotheses.

Statement (recalled). Let `F` be a finite field with `q` elements and let `f ∈ F[X, Y]` be
absolutely irreducible with `∂f/∂X ≠ 0`, `∂f/∂Y ≠ 0`, `2 ≤ n = deg_Y f ≤ m = deg_X f`. Let
`r(x)` be the number of `y ∈ F` with `f(x, y) = 0`. For every `M > 0` with
`M²(n² + 1) + (M + m) n² < q` and `M n ≤ q`, there exist a set `s ⊆ F` and polynomials
`h₁, h₂ ∈ F[X]` such that:

- `q < #s + 2 m n`;
- `r(x) ≤ n` for every `x`;
- `h₁ ≠ 0`, `h₂ ≠ 0`, with `deg h₁ < q (M + 2m(n - 1) + 1)` and
  `deg h₂ < q ((n - 1) M + 2m(n - 1) + 1)`;
- for every `x ∈ s`, `h₁` vanishes at `x` to order at least `M r(x)` and `h₂` to order at least
  `M (n - r(x))`.

This is the auxiliary-polynomial part of Schmidt, *Zur Methode von Stepanov* (Acta Arith. 24,
1973), Sections 4–6.

## Proof

Write `fh = (equivMvPolynomial F).symm f ∈ F[X][Y]`.

1. `bivariateModel` (`BivariateModel.lean`) gives the following facts:
   - `natDegree fh = n`, and the coefficients of `fh` have degree `≤ m`;
   - `fh` is irreducible over `F` and over `AlgebraicClosure F`;
   - `fh_Y ≠ 0`;
   - for every `x`, `fh(x, Y) ≠ 0`, and `r(x)` is the number of distinct roots of `fh(x, Y)`
     in `F`.
2. Parameters: `d = ⌊q/n⌋ - m n`, `N₁ = ⌊(M + m)/n⌋`, `N₂ = ⌊(n - 1)(M + m)/n⌋`.
   `stepanovParameterArithmetic` (`ParameterArithmetic.lean`) gives five inequalities:
   - `n d + m (n - 1)² < q`;
   - the two dimension inequalities required by `exists_normPoly_rational` and
     `exists_normPoly_nonrational` (`Assembly.lean`) with `N = N₁` and `N = N₂`;
   - `(n - 1)(q + 1) m + n (d + q N₁) < q (M + 2m(n - 1) + 1)` and
     `(n - 1)(q + 1) m + n (d + q N₂) < q ((n - 1) M + 2m(n - 1) + 1)`.

   Together with `M ≤ q`, which follows from the size hypothesis, these give `h₁` and `h₂`.
   The last two inequalities turn the degree bounds of `Assembly.lean` into the required ones.
3. `exists_goodSet_discriminant` (`GoodSet.lean`) gives a nonzero `Δ ∈ F[X]` with
   `deg Δ ≤ (2n - 1) m`. For every `x` with `Δ(x) ≠ 0`, `fh(x, Y)` has degree `n` and is
   separable. Take `s = {x : Δ(x) ≠ 0}`. Its complement lies in the roots of `Δ`, so it has
   at most `(2n - 1) m < 2 m n` elements, which gives `q < #s + 2 m n`.
4. The bound `r(x) ≤ n` holds because the number of distinct roots of `fh(x, Y) ≠ 0` is at most
   its degree, which is at most `n`.
5. Let `x ∈ s`.
   - For `h₁`, use the set `T` of rational roots `y` of `fh(x, Y)`. Each `y ∈ T` satisfies
     `fh(x, y) = 0`. Separability gives `fh_Y(x, y) ≠ 0` (`ev_derivative_ne_zero`). Then
     `M r(x) ≤ mult_x h₁`.
   - For `h₂`, use the set `T ⊆ F̄` from `nonrationalRoots` (`RootTools.lean`). Its elements
     are roots `y` of `fh(x, Y)` with `fh(x, y^q) = 0` and `y^q ≠ y`, and
     `#T ≥ n - r(x)`. The leading coefficient of `fh` does not vanish at `x` because
     `deg fh(x, Y) = n`. Then `M (n - r(x)) ≤ M #T ≤ mult_x h₂`.

Helper lemmas in this file: `ev_self_eq` (for `y ∈ F`, `ev x y P` is `P(x, Y)` evaluated at
`y`) and `ev_derivative_ne_zero` (separability of `P(x, Y)` gives `P_Y(x, y) ≠ 0` at a root
`y` in any extension field).
