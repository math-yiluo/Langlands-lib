# Generic gamma assembled from the actual local factors

This module constructs `genericSymmetricGammaUnit` for generic complex
representations of GL_(r+1) and GL_(n+1) over a p-adic field. The field and
representation carriers have independent universes `uF`, `uV` and `uW`.
Every positive rank is included. Inputs are the nontrivial unitary additive
character, the supplied additive Haar measure with its self-duality proof,
and the two original genericity proofs. No analytic, quotient-measure,
epsilon-existence, L-existence or transformed-genericity premise is added.

All field structures use the canonical p-adic topology and its Borel space.
A private helper obtains a basis of open additive subgroups from the valuation's
open submodules. This supplies the nonarchimedean additive-group structure and
the total disconnectedness needed to state self-duality; it adds no input.

The construction uses the actual published generic epsilon unit, the original
L-unit and the inverse-transpose L-unit:

```text
epsilon * reflect(dual L) / original L.
```

Reflection is the shared `RationalReflection.subst` at
`LocalFactor.residueReflection F`, whose value is `q^(-1)` for the canonical
residue cardinality `q`. Thus `X = q^(-s)` is changed to `q^(-1)/X`,
corresponding to `1-s`. The dual L-unit is for the actual
`inverseTransposePullback` pair, at `psi.scale (-1)` and the unchanged Haar
measure. All three factors use the existing larger-rank-first convention.
Equal ranks retain the supplied order.

## Intrinsic construction and comparison

`genericSymmetricGammaUnit_eq_expression` rewrites the L-units as reciprocals
of their normalized polynomials. Reflection preserves inversion and substitutes
its reflected variable in the dual polynomial. Elementary field algebra gives
`rationalGammaExpression` with the actual epsilon data and actual original and
dual polynomials.

`genericSymmetricGammaUnit_isPadic` instantiates the published
`symmetricGammaExpression` theorem with those three intrinsic certificates.
Its construction premise is supplied by
`genericSymmetricGammaConstructionInput`, which already derives the original
and dual analytic conclusions and uniform epsilon existence from the two
genericity proofs and supplied self-dual measure. The resulting certificate is
the unchanged `IsPadicSymmetricGammaFactor`, including compatible-measure and
nonzero-functional witnesses and its universal integral equations.

`genericSymmetricGammaFactor_eq_unit` applies the existing intrinsic uniqueness
theorem and unit extensionality to identify this explicit assembly with
`genericSymmetricGammaFactor`. The following rational equality exposes the
same expression for that existing constructor. This is a construction
comparison; it introduces no new rank-exchange or multiplicativity theorem.

## Spectral interface

`mem_genericSymmetricGammaRegularDomain_of_dualPolynomial` proves that
nonvanishing of the actual dual polynomial at `q^(-(1-s))` implies membership
in the existing gamma regular domain. It uses the shared regularity theorem
for `rationalGammaExpression` and nonvanishing of the spectral point.
The existing domain is still defined by the reduced rational denominator;
cancellation may make it larger than this sufficient polynomial domain.

`genericSymmetricGammaValue_eq_localFactors` evaluates on this polynomial
domain. The complex value is the actual `genericSymmetricEpsilonValue` times
the original polynomial at `q^(-s)`, divided by the dual polynomial at
`q^(-(1-s))`. The proof applies the published rational evaluation theorem,
the spectral reflection identity and the defining epsilon value formula.
No nonvanishing of the original polynomial is required, so gamma zeros are
permitted. This formula is not asserted at a zero of the displayed dual
denominator, even if cancellation makes the reduced gamma value regular.

## Source and provenance

This is derived assembly of the Library's actual generic factor constructors,
`SymmetricGammaExpressionProof`, and the shared rational reflection and
evaluation lemmas. Imported public proofs are dependencies.

The original source is H. Jacquet, I. I. Piatetski-Shapiro and J. A. Shalika,
*Rankin-Selberg Convolutions*, American Journal of Mathematics 105 (1983),
367–464, registered as `jpss-1983-rankin-selberg`, SHA256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
The retained original is
`/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Rankin-Selberg Convolutions--1983.pdf`.
Section 2.1, printed page 386, formula (4) (retained PDF page 21), gives
the inverse-transpose and inverse-character convention. Theorem 2.7(ii)–(iii),
printed pages 390–391 (PDF pages 25–26), gives the normalized original/dual
polynomials and epsilon equations. Rearranging those equations yields the
gamma ratio used here, with the central-character sign remaining outside
gamma. Section 2.12, printed page 403 (PDF page 38), gives the larger-first
L and epsilon convention; the gamma convention is its derived consequence.
These original pages were read visually. No source-specific errata file was
found in the project literature or Library notes.

The supplied self-dual measure remains explicit mathematical input. This
module does not construct such a measure, identify inverse-transpose pullbacks
with smooth contragredients, descend factors to isomorphism classes, or extend
the constructions to nongeneric representations. Character transport, twists,
factor laws and nongeneric existence retain their separate responsibilities.
