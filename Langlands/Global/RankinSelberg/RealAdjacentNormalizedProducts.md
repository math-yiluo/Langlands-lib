# Normalizing the real adjacent-rank finite product sums

The finite expansion of the real adjacent-rank integral is a sum of products of a smaller
equal-rank integral and a square matrix integral. This module combines normalized equations of
the two kinds of factors into the normalized equation of the sum. It is the real counterpart of
the Library's `ComplexAdjacentNormalizedProducts`.

## Results

- `realPairLFactor_cons`: `realPairLFactor (x :: xs) ys` is the product of
  `realPairLFactor [x] ys` and `realPairLFactor xs ys` (as reciprocal-entire functions).
- `realPairEpsilon_cons`: likewise `realPairEpsilon (x :: xs) ys b c hc s` is the product of the
  epsilon factors of `[x] × ys` and `xs × ys`.
- `realAdjacentNormalizedProducts`, the proof of `RealAdjacentNormalizedProductsStatement`. Let
  `x` be a real block, `xs`, `es` block lists, `b ∈ ℝˣ`, `c > 0`, and let `sA`, `κ`, `κd`, `sign` be
  complex numbers with `κd · sA = sign · κ`. Let `A_j, Ad_j` (`j < m`) satisfy
  `HasRealPairNormalizedGrowth` for `xs × es` and their blockwise duals with parameters `b`, `c`
  and sign `sA`, and let `Z_j, Zd_j` satisfy it for `[x] × es` with sign `1`. Then the pair
  `s ↦ κ Σ_j A_j(s) Z_j(s)` and `s ↦ κd Σ_j Ad_j(s) Zd_j(s)` satisfies
  `HasRealPairNormalizedGrowth` for `(x :: xs) × es` with sign `sign`.

## Proof

Take the entire normalizations `N_j` of `A_j` and `M_j` of `Z_j` (and those of the dual
functions). The normalizations proposed for the sums are `κ Σ_j N_j M_j` and `κd Σ_j Nd_j Md_j`. They are
entire, and they have exponential growth on vertical strips because the class of such functions
is closed under products, finite sums and scalar multiples. On the maximum of the finitely many
half-planes of the hypotheses they agree with the denominator of the pair `L`-factor of
`(x :: xs) × es` times the sums, because the denominator splits by `realPairLFactor_cons`; the
same holds for the dual lists. The reflected equation follows from the two given equations and
`realPairEpsilon_cons`, since `κd · sA = sign · κ`.

## Relation to the literature

H. Jacquet, *Archimedean Rankin–Selberg integrals* (2009), registered as
`jacquet-2009-archimedean-rankin-selberg`, §8.3, pp. 59–60: each term of the expansion is a
product of an integral for the pair `(n − 1, n − 1)` and a matrix integral, and the analytic
properties and the functional equation of the sum follow from those of the factors. The scalars
`κ` and `κd` carry the signs that appear in the unfolding of the ordinary and dual integrals; the
formal statement uses the Library's entire normalizations with exponential strip growth.
