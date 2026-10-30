# Cumulative-product coordinates for the JPSS torus

`Langlands.RankinSelberg.RootCoordinateChangeStatement F T n` is a
proposition for every p-adic field, every supplied topological data `T`, and
every natural number `n`. The matrix rank is `n + 1`, including rank one. The
field universe is unrestricted. This module supplies only the proposition
definition; it is proved, with exactly these parameters, by
`Langlands.RankinSelberg.rootCoordinateChange` in
[RootCoordinateProof](RootCoordinateProof.md), as recorded in the final
section.

Write `r = n + 1` and use zero-based indices. On the torus
`A = (F×)^r`, the two explicitly specified maps are

\[
  \tau(a)_i=\prod_{j\geq i}a_j,\qquad
  \rho(b)_i=b_i/b_{i+1}\ (i<r-1),\qquad
  \rho(b)_{r-1}=b_{r-1}.
\]

The statement says that both maps are continuous, they are inverse to one
another, and `τ` preserves multiplication. Thus these are the actual
continuous group coordinate changes, with no arbitrary equivalence supplied
as a hypothesis.

Equip each unit-group factor with `localMultiplicativeHaar F.Carrier`, using
the valuation and topology from `T`, and its Borel measurable structure. Let
`dA` be the finite product measure `Measure.pi` of these measures. The target
asserts `Measure.map τ dA = dA`. Each factor's integral-unit subgroup has
mass one. This normalization matters: `τ` and `ρ` preserve the product of
integral-unit groups, so Haar uniqueness gives the asserted equality
without an unspecified scalar. This is the argument implemented by the
published proof.

For each `a`, put `D(a) = Iwasawa.diagonalUnits (τ a)`. The remaining clauses
state the explicit formulas needed by the integral:

- The simple-root ratios of `τ a` are `a_i` for `i < r-1`, and its final
  coordinate is `a_(r-1)`.
- `det D(a) = ∏ᵢ a_i^(i+1)`, as an equality in the field.
- For every invertible matrix `k`, `lastRow (D(a) * k)` is
  `a_(r-1)` times `lastRow k`.
- The upper-Borel modulus in ordinary diagonal coordinates satisfies
  `∏_(i<j) |τ(a)_i / τ(a)_j| = ∏ᵢ |a_i|^((i+1)(r-1-i))`, with
  `|·| = T.normalizedAbs`. In rank one this is the empty product, equal to
  one. The natural-number subtraction in Lean is nonnegative because
  `i : Fin (n + 1)`.

These formulas keep the modulus itself positive and un-inverted. The
quotient-Iwasawa integral uses its inverse. No quotient integration formula,
Whittaker expansion, convergence, rationality, or denominator result is
asserted by this statement or established by its proof.

The provenance is derived from Jacquet–Piatetski-Shapiro–Shalika,
*Rankin–Selberg Convolutions* (1983), proof of Theorem 2.7, printed pp. 391–392.
Display (4) on p. 391 specifies exactly the cumulative-product diagonal
matrix. Displays (3) and (5) retain the inverse Borel modulus and final-row
test. The integral following (5), and then (6), use determinant exponents
`1, …, r` and product multiplicative measure. The statement isolates and
makes explicit the coordinate and normalization facts used in those steps;
it is not a separately named theorem in the source. The modulus exponents
count the pairs of indices across each simple root.

Source: `jpss-1983-rankin-selberg`, SHA256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`,
printed pp. 391–392, displays (3)–(6).

## Proof in the Library

The theorem `Langlands.RankinSelberg.rootCoordinateChange` has type

```lean
{p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
  (T : F.TopologicalData) (n : ℕ) :
  RootCoordinateChangeStatement F T n
```

for an arbitrary universe `uF`. Its type adds no hypothesis, so every clause
above holds for every supplied topology and every rank `n + 1`: continuity,
the two inverse identities and multiplicativity, `Measure.map τ dA = dA`, the
simple-root and final coordinates, the determinant and last-row formulas,
and the positive-modulus formula. These are coordinate facts only.
Integration on the left-unipotent quotient is the separate
`QuotientIwasawaIntegrationStatement`, proved by
`quotientIwasawaIntegration`, and its transport to these coordinates is the
separate conditional `QuotientRootIntegrationStatement`. Convergence of the
JPSS Rankin–Selberg integrals is not part of this result.
