# Full-rank simple-root and last-coordinate Mellin convergence

This internal supporting unit proves convergence of the separated diagonal
majorant used for the full-rank Whittaker–Schwartz kernel. It derives its
estimates from `AdelicSchwartzMellinProduct`, the adjacent-root torus coordinate
identities, and `AdelicSimpleRootGaugeHaarModulus`. It makes no new
external-source attribution.

Let `r` be any natural number, including zero. Write `a_i = d_i/d_(i+1)`
for `i < r`, and `a_r = d_r`. For a number field `F` with compact additive
adelic quotient, a Haar measure `mu` on the `(r+1)`-fold idele torus, a
Schwartz–Bruhat function `phi` on `r` additive adele coordinates, and a
Schwartz–Bruhat function `psi` on one additive adele coordinate, the theorem
`lintegral_gaugeSchwartzTorusMajorant_lt_top_of_large` proves finiteness of

```text
integral_d delta(d)^(-1) * |a_0 ... a_(r-1)|^(-tau)
  * ||phi(a_0,...,a_(r-1))|| * ||psi(d_r)|| * |det(diag d)|^sigma
```

Here the integral is the nonnegative extended lower integral, `delta` is the
actual diagonal unipotent Haar modulus, and all idele norms are the Library's
normalized full absolute value. The Lean expression uses
`gaugeDiagonalInverseHaarWeight`, definitionally the inverse of
`AdelicDiagonalUnipotentModulus.diagonalModulus` coerced to `ENNReal`.
The required half-plane is

```text
0 <= tau,
sigma > tau + 3 + sum_(j=0,...,r) (j+1)*(r-j).
```

The threshold is independent of both Schwartz functions and of the Haar
normalization. No gauge, right-compact invariance, or quotient integration
hypothesis enters this torus theorem.

The proof first establishes
`AdelicSchwartzMellin.lintegral_split_schwartz_mellin_lt_top`. The published
product-majorant theorem bounds the first Schwartz function by a finite
scalar times a product of one-coordinate Schwartz functions. When `r = 0`,
the row space is a singleton: its norm is retained as that finite scalar,
and the empty product is one. The supplied final-coordinate Schwartz
function is then appended with `Fin.lastCases`. Each weighted coordinate
kernel is measurable. Finite-product Tonelli and the published rank-one
Mellin estimate give finiteness for product Haar when every exponent exceeds
three. Haar uniqueness transfers this finiteness to the supplied arbitrary
Haar measure. This argument asserts no equality of Haar normalizations.

The definition `gaugeFullRankMellinExponent` records the coordinate exponent

```text
(j+1)*sigma + b_j - (j+1)*(r-j),
b_j = -tau for j < r, and b_r = 0.
```

`gaugeFullRank_scalarWeight` proves the exact weight identity using the
published determinant formula in adjacent-root coordinates, the actual
inverse Haar weight formula, finite-product real powers, and addition of
exponents of positive reals. The final coordinate therefore has exponent
`(r+1)*sigma`; it receives no simple-root gauge power or Haar-modulus power.

`gaugeFullRankMellinExponent_gt_three` uses nonnegativity of `tau` and the
sum of the nonnegative root multiplicities to show every coordinate
exponent exceeds three in the stated half-plane. The final theorem applies
the split-coordinate result with these exponents, transports convergence
through `GaugeTorusCoordinates.lintegral_blockRoots_lt_top_iff`, and uses
the exact scalar identity to recover the displayed integrand. The coordinate
transport preserves finiteness for arbitrary Haar normalization.

This unit supplies the uniform torus convergence input. The compact-uniform
kernel bound, the actual Whittaker quotient application, and the final
unchanged `WhittakerSchwartzGaugeStatement` are separate results.
