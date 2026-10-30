# Reduced value set for the positive-rank rank-one comparison

Module `Langlands.Representation.RankinSelberg.RankOneMatrixWhittakerComparisonValues`.
This module only makes definitions. It proves nothing and assumes nothing.

## Purpose

The positive-rank branch (`n = m + 1`, actual rank `m + 2`) of
`RankOneMatrixWhittakerComparisonStatement` compares two value sets:

- the rank-one character zeta values `characterZetaValues q ψ abv μ 1 (m + 1) σ`
  (the JPSS integral `Ψ(s, W)` of JPSS 1983, Section 5.2, equation (1), printed p. 420);
- the shifted Godement–Jacquet matrix values `GodementJacquet.Padic.whittakerRationalValues`
  (JPSS 1983, Section 5.2, equations (2)–(3), printed pp. 420–421).

Both are identified, in separate proof modules, with the single explicit set defined
here. The set is internal to this proof and is not taken from the literature. It
writes the integral `Ψ(s, W)` with the trivial character as an integral over the
normalized Haar measure of `GL₁`, with no quotient and no rectangular variable.

## Definitions

- `rankOneEmbedding m g` is the matrix `diag(det g, 1, …, 1)` in `GL_(m+2)`, for
  `g ∈ GL₁ = GL_(0+1)`. It is built with `Iwasawa.diagonalUnits` from the diagonal
  `Fin.cons (det g) 1`.
- `rankOneModelIntegrand ψ abv σ ℓ w s g` is
  `W(diag(det g, 1, …, 1)) · |det g|^(s - (m+1)/2)`. Here `W` is the actual model
  function `glModelFunction ψ (m + 1) σ ℓ w` of a vector `w` of the coefficient image
  of the specified functional `ℓ`. The weight is the published `determinantWeight`,
  and `(m + 1)/2` is the complex number `((m + 1 : ℕ) : ℂ) / 2`. This is the exponent
  `s - n/2` of the statement with `n = m + 1`.
- `rankOneModelValues q ψ abv μ₁ σ ℓ` is the set of rational functions `R` for which
  some model vector `w` has an integrand that is absolutely integrable for `μ₁` for
  every `s` in some right half-plane, and whose Bochner integral has the rational
  continuation `R`. The continuation uses the published `HasRationalContinuation q`.
  The measure `μ₁` on `GL₁` is an explicit argument. In applications it is
  `generalLinearHaar F 0`.

## Scope

The set ranges over the coefficient image of one specified functional. It does not
range over all equivariant functions. Convergence is a requirement on each element,
not a theorem. No rationality, common denominator, admissibility or
finite-generation statement is made.
