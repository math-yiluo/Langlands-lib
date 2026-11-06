# Coordinate translations generate Steinberg monomial boxes

This derived unit works over an infinite field `k` and an independently sized
variable type `σ`. The endomorphism `axisTranslation i t` is the actual algebra
substitution which sends `X i` to `X i + C t` and fixes every other variable.
It is defined by `MvPolynomial.aeval`, then regarded as a linear map.

For an exponent vector `b`, the polynomial family
`axisMonomialFamily i b` is
`C (monomial (b.erase i) 1) * (X + C (MvPolynomial.X i)) ^ b i`,
where the outer polynomial variable is the translation parameter. Evaluating
this family at `MvPolynomial.C t` gives the translate of `monomial b 1`.
Its coefficient at `n` is the monomial with exponent `b - single i n` and
coefficient `choose (b i) n`, cast to `k`. Subtraction of exponents is truncated
natural subtraction; when `n > b i`, the binomial coefficient is zero.

The auxiliary coefficient-extraction theorem applies to polynomials with
coefficients in any commutative `k`-algebra. If all evaluations at scalar
parameters belong to a `k`-subspace, every coefficient belongs to that subspace.
The proof applies each linear functional annihilating the subspace to the
coefficients. Linearity and scalar multiplication identify the resulting scalar
polynomial evaluations. A polynomial over an infinite field which vanishes at
every scalar is zero, and dual separation recovers subspace membership.

Consequently, a subspace stable under every `axisTranslation i t` contains the
binomial multiple of each lowered monomial whenever it contains the original
monomial. Suppose all `choose (N i) n` are nonzero for `n ≤ N i` and the subspace
contains the top monomial with exponent `N`. Induction on the finite support
of a lowering vector `a ≤ N` gives the monomial with exponent `N - a`.
At each step, the new coordinate has not yet been lowered, so its exponent is
still `N i`; coefficient extraction and multiplication by the inverse nonzero
binomial coefficient lower it by the required amount. Taking `a = N - m`
recovers each `m ≤ N`, and the restricted-support monomial basis gives
`monomialBox N ≤ W`.

In prime characteristic `p`, the published
`RankOneSteinberg.choose_steinberg_cast_ne_zero` supplies the needed nonzero
coefficients when each positive coordinate of `N` equals `p^r - 1`.
Coordinates outside the support have exponent zero and only require
`choose 0 0 = 1`. The result includes `r = 0`, when the box contains only
constant polynomials. If a finite-dimensional space has a translation-stable
polynomial image containing the top monomial, inclusion of this box and the
range dimension bound give dimension at least
`∏ i ∈ N.support, (N i + 1)`.

The provenance is internal polynomial linear algebra and the imported proved
rank-one binomial identity. This unit derives lower-box membership from actual
coordinate substitutions, with top-monomial membership and translation stability
explicitly assumed. It does not identify these translations with root-group
actions for a general reductive group, construct root coordinates, prove a
support bound, or prove the general Steinberg big-cell statement.
