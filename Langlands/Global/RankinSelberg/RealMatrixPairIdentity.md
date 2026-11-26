# The determinant-twisted real matrix equation with pair factors

This module restates the determinant-twisted real square matrix functional equation of
`RealMatrixTwistedFunctionalEquation` with the published pair `L`- and `ε`-factors of real
block presentations, in the form `RealJacquet.PairMeromorphicIdentity` used by the equal-rank
expansion of Jacquet §8.2 (`RealLocalEqualJacquetExpansion`).

## Definitions

`HasRealMatrixPairIdentity μ f Φ fd Φd xs ys b sign` keeps the convergence and continuation
clauses of `HasRealMatrixEquation`. There is a real `σ` and functions `M` and `Md` such that:

- the normalized matrix zeta kernels of `(f, Φ)` and `(fd, Φd)` are `μ`-integrable for `σ < Re s`;
- the two normalized matrix integrals are holomorphic on that half-plane and equal `M` and `Md` there;
- `M` and `Md` are meromorphic on `ℂ`.

Its equation clause is replaced by `RealJacquet.PairMeromorphicIdentity xs ys b sign M Md`. Off
a discrete set, this is

`D(s)⁻¹ · Md(1 − s) = sign · ε(s) · Dd(1 − s)⁻¹ · M(s)`.

Here `D` is the reciprocal-entire denominator of `realPairLFactor xs ys`, so `D⁻¹` is
`L(s, xs × ys)`. `Dd` is the denominator for the dual lists, the blockwise
`RealLocalJacquet.dualBlock` inverses. `ε(s)` is `realPairEpsilon xs ys` at additive parameter
`b` and Haar scale `√|b|`.

## Statement

`RealMatrixPairIdentityStatement`: let `n = r + 1`, `μ` a Haar measure on `GL_n(ℝ)`, `κ` an
s-finite Haar measure on `O(n)`, and `es` a list of real blocks of total rank `n`. Let `f` be a
smooth section of the position principal series of `expand es` (each induced block replaced by
its two position characters; the inducing characters are those of `es`), and `ℓ` a linear form
with `HasCompactDerivativeBound`. For a real character datum `d`, a Schwartz function `Φ` on
`n × n` real matrices and `b ∈ ℝˣ`, put `F(g) = d(det g) · ℓ(translate g f)`. Then
`HasRealMatrixPairIdentity μ F Φ (F ∘ inverseTranspose) (matrixTransform b Φ) [character d] es b 1`
holds: the matrix integral of `(F, Φ)` and its inverse-transpose dual with the `b`-Fourier
transform continue meromorphically and satisfy the pair identity for `[d] × es` with sign `1`.
`realMatrixPairIdentity` proves it.

## Proof

1. `exists_expand_eq_map_character`: `expand es` is a list `cs.map character` of character
   blocks. This is checked by unfolding `expand` on each block. `realRank_map_character` and
   `realRank_expand` give `cs.length = n`.
2. `realMatrixTwistedFunctionalEquation`, applied to the list `expand es`, gives the
   continuation and the codiscrete equation with the torus factors `torusL e u`,
   `torusL e (−u)` and `E`, where `e_i = sign_i + parity(d)` and `u_i = exponent_i + exponent(d)`
   at the positions of `cs.map character`.
3. `prod_range_positions` and `prod_fin_positions` turn a product over the `n` positions of
   `cs.map character` into the product over the list `cs`. The tensor product of the character
   block `d` with a character block `χ` is the character block `d.mul χ`
   (`pairBlocks_character`), with added parity and exponent. So:
   - `torusL_eq_pair`: `torusL e u s` is the inverse of the denominator of
     `realPairLFactor [d] (cs.map character)`.
   - `torusL_neg_eq_pair`: `torusL e (−u) z` is the inverse of the dual pair denominator, using
     `dualBlock (character χ) = character χ⁻¹`.
   - `torusEpsilon_eq_pair`: `E(s)` equals `realPairEpsilon [d] (cs.map character) b √|b| s`.
     This uses the Library closed formula `coe_realEpsilon`, `(√|b|)^n · |b|^{n(s−1)} = |b|^{n(s−1/2)}`
     (`sqrt_scale_eq`), the character values `(dχ)(b) = χ(b) d(b)` and the standard phases
     `i^{parity}`.
   This gives `PairMeromorphicIdentity [d] (cs.map character) b 1 M Md`.

   Steps 1–3 form the public lemma `realMatrixPairIdentity_expand`. It gives the same
   conclusion as the statement below, `HasRealMatrixPairIdentity … [character d] (expand es) b 1`,
   but for the list `expand es` itself rather than `es`. This is the factor form used by
   `RealMatrixNormalizedGrowth`.
4. `pairMeromorphicIdentity_of_multiplier`: a pair identity transfers between two presentations
   whose `RealPrincipalSeries.pairMultiplier` agree off a discrete set. Where both primal
   denominators are nonzero (`denominator_codiscrete`), the identity is equivalent to
   `Md(1 − s) = sign · pairMultiplier(s) · M(s)`. The Library's `pairMultiplier_expand` (block
   versus position Gamma comparison, including induced blocks) for `[d]` and `es` finishes the
   proof, since `expand [character d] = [character d]`.

## Scope

Only coefficients of the smooth position principal series of `expand es` with a supplied compact
derivative bound, multiplied by a determinant character, are covered. The identity is the
multiplied-out continuation equation of the explicit convolved-pair argument behind the matrix
equation. It is not a theta identity for arbitrary Jacquet pairs, does not compare with
Whittaker or Langlands-quotient models, and gives no vertical-strip bounds.

Source: Jacquet, *Archimedean Rankin–Selberg Integrals* (2009), §4.7, Proposition 4.4,
pp. 30–31, in its use in §8.2, pp. 56–58 (literature id `jacquet-2009-archimedean-rankin-selberg`).
The factor comparison is the Library's `RealPrincipalSeries.pairMultiplier_expand`.
