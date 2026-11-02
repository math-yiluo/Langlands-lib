# Compactness of Hilbert–Schmidt operators

`Langlands.Analysis.OperatorIdeals.hilbertSchmidtCompact` proves the exact
proposition `HilbertSchmidtCompactStatement`. For complex Hilbert spaces
`E : Type u` and `F : Type v`, every bounded complex-linear map
`A : E →L[ℂ] F` satisfying the existing `IsHilbertSchmidt A` is a compact
operator in Mathlib's sense. The universes are independent, and no
separability or endomorphism assumption is introduced.

The proof uses the actual Hilbert basis in the existential witness. Its
private helper `opNorm_le_basis_sum` proves

`‖T‖ ≤ sqrt (∑' i, ‖T (b i)‖²)`

whenever the squared-image family is summable on a Hilbert basis `b`.
For a finite basis expansion of a vector `x`, the triangle inequality and
finite Cauchy–Schwarz bound the square of its image norm by the product of
the sums of squared coefficients and squared image norms. Bessel's
inequality bounds the first factor by `‖x‖²`; nonnegativity and summability
bound the second by the full sum. `HilbertBasis.hasSum_repr` and continuity
of `T` pass this inequality to `T x`, and the operator-norm bound follows.

For a finite set `s` of basis indices, `basisTruncation` is the continuous
linear map

`R_s x = ∑ i ∈ s, inner ℂ (b i) x • A (b i)`.

Each summand is a compact operator: the scalar functional
`innerSL ℂ (b i)` has locally compact codomain `ℂ`, so Mathlib's
`isCompactOperator_of_locallyCompactSpace_dom` makes it compact (despite
its name, that lemma assumes local compactness of the codomain), and its
composition with `ContinuousLinearMap.toSpanSingleton ℂ (A (b i))` remains
compact by `IsCompactOperator.clm_comp`. The submodule of compact operators
is closed under finite sums, so `R_s` is compact.

Orthonormality gives `R_s (b i) = A (b i)` for `i ∈ s` and zero otherwise.
Consequently the squared-image family for `A - R_s` is precisely the
indicator of the complement of `s` applied to the original squared-image
family. It is summable, and the preceding helper gives the tail bound

`‖A - R_s‖ ≤ sqrt (∑' i : { i // i ∉ s }, ‖A (b i)‖²)`.

Mathlib's `tendsto_tsum_compl_atTop_zero`, continuity of the nonnegative
square root and the squeeze theorem make the right side tend to zero
along all finite subsets ordered by inclusion. Thus `R_s` tends to `A`
in operator norm. `isCompactOperator_of_tendsto` supplies compactness of
the limit, using completeness of the codomain.

The final theorem unpacks `IsHilbertSchmidt A` and applies this argument
to its witnessing basis. The proof does not use basis independence, a
chosen countable enumeration, spectral theory, or a trace-class assertion.
In particular it also covers zero spaces and arbitrary-index bases.

The original-source assertion and its scope are documented in the unchanged
statement pair: Getz–Hahn, *An Introduction to Automorphic Representations*
(2024), Definition 9.1.1 and (9.3), printed p. 240, Exercise 9.3, p. 267,
and the use in Corollary 9.3.2, p. 247. These original passages were read
directly, together with the complete five-page October 2026 errata, whose
Chapter 9 entries (the §9.2 quotient notation and the §9.5 remark on the
proof of Theorem 9.1.2) do not change these operator assertions. The source uses
separable endomorphisms; the arbitrary-index rectangular extension is
derived here by the explicit finite-rank argument above. This implementation
is an internal proof of the existing proposition, not a transcription of a
proof supplied in the source.
