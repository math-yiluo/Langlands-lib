# The rank-one L-polynomial of an unramified character

Author: Worker 1738.

For a p-adic field `F`, a unit `z : ℂˣ`, any unitary additive character `ψ`
and any additive Haar measure `ν`, the theorem
`Langlands.RankinSelberg.unramifiedRankOneLPolynomial_eq` identifies every
supplied certificate

```lean
IsPadicSymmetricLPolynomial F ψ ν
  (characterRepresentation
    (Correspondence.determinantQuasiCharacter F 1 (Unramified.character F z)))
  (characterRepresentation (Correspondence.determinantQuasiCharacter F 1 1)) P
```

with `P = 1 - C (z : ℂ) * X`. The field topology, valuation and local-field
structure are the canonical local instances of `F`. The additive character
need not be nontrivial, the measure need not be self-dual, and the
multiplicative character need not be unitary. This theorem identifies a
supplied certificate; it does not assert existence of pair certificates.

The proof computes the scalar Mellin generator and transports the supplied
equal-rank `GL₁ × GL₁` certificate to that generator.

## Scalar Mellin computation

All three scalar lemmas use `F.canonicalTopologicalData`, the normalized
multiplicative Haar measure `localMultiplicativeHaar F.Carrier`, and the actual
character `Unramified.character F z`. The scalar Mellin rank parameter is one.

`unramifiedScalarMellin_clears` proves that multiplying any scalar Mellin
rational value by the image of `1 - C (z : ℂ) * X` gives a Laurent polynomial.
The published `finiteFunctionShellSeries` gives a uniformizer `π` of order
one, a common convergence bound, and the shell coefficients

```text
c(n) = integral over integral units u of Φ(π^n u) χ(π^n u).
```

The integral units have measure one and order zero. The published
`schwartzBruhatValuationBounds` implies that `Φ(π^n u) = Φ(0)` for
sufficiently large `n`, uniformly in those units. Since `χ(π^n u) = z^n`,
one gets `c(n) = Φ(0) z^n` on that tail. After increasing the start index
to satisfy both bounds, this tail solves the first-order recurrence
`c(n+1) = z c(n)`. The published
`Analysis.eventuallyRecurrentLaurentSeriesStatement_proof` supplies a rational
function with denominator `1 - C z * X` and its Laurent clearing identity.
The shell integral and that rational function agree on a right half-plane.
Uniqueness of rational continuation identifies it with the given rational
value, establishing the claimed clearing identity.

`unramifiedScalarMellin_reciprocal_mem` constructs the Schwartz–Bruhat
indicator of the integer ring, using its compactness and openness. On a shell
of order `n`, that indicator is one exactly when `0 ≤ n`. Its shell
coefficients are therefore `if 0 ≤ n then z^n else 0`. For a sufficiently
small nonzero spectral value `w`, the shell sum is
`∑ n : ℕ, (z*w)^n = (1-z*w)⁻¹`. The proof obtains the integer-indexed sum
from the published Laurent-series splitting lemma, applies the usual complex
geometric-series sum, and checks regularity of the rational reciprocal by
its nonzero denominator. This proves that the reciprocal of the image of
`1 - C z * X` itself is an actual scalar Mellin rational value.

`unramifiedScalarMellin_isNormalizedGenerator` combines the clearing identity,
reciprocal membership and constant coefficient one using
`isNormalizedGenerator_iff`. Thus it computes the exact normalized generator
of the span of all the scalar Mellin values.

## Transport of the pair certificate

The two determinant-character representations in the main theorem are
definitionally the corresponding `rankOneCharacter` representations.
The first has full Whittaker type by
`rankOneCharacter_isOfWhittakerType`. Its one-dimensional underlying complex
space makes it irreducible: every subrepresentation has underlying submodule
either zero or the full space. A nonzero Whittaker functional therefore gives
the representation equivalence `glModelEquiv` with its coefficient model.

The published
`GodementJacquet.Padic.isMatrixNormalizedGenerator_model_of_pair` converts
the supplied pair certificate to the matrix normalized-generator property
for that model. The published `GodementJacquet.matrixRationalValues_equiv`
transports it back along `glModelEquiv`, and
`GodementJacquet.Padic.tateMatrixRationalValues_eq_scalar` identifies the
matrix rational values with the scalar Mellin values computed above.
Uniqueness of normalized generators then gives `P = 1 - C z * X`.

## Provenance

This is an internal specialization of the published shell-integration,
eventual-recurrence, Godement–Jacquet model comparison and Tate matrix
comparison results named above. The elementary spectral helpers adapt the
complex-power and right-half-plane arguments in
[`TateScalarMellin`](../GodementJacquet/TateScalarMellin.md). The
irreducibility helper uses the same elementary submodule argument as
`Classification.OrderedMultisegmentHeadReduction.isIrreducible_of_linearEquiv_complex`,
specialized to the underlying space `ℂ`. No additional literature claim or
axiom is introduced.
