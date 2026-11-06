# Actual Speh blocks and Tadic unitary-dual exhaustion

Author: Worker 1745. This pair defines actual induction constructions and
Prop-valued statement targets. It proves none of the classification assertions
and assumes no quotient existence or classification theorem in a constructor,
structure field, or axiom.

## Actual parameters and normalization

Fix a prime `p`, `F : PadicField.{uF} p`, and `T : F.TopologicalData`.
The field and representation universes are independent. All representation
carriers in this interface lie in `Type (max uF uV)`. Normalized induction
preserves that universe. No finite-dimensionality condition is imposed on
these carriers.

All new names lie in `Langlands.Classification`. `SpehDatum F T` contains
positive integers `rank = r` and `length = k` and an actual smooth complex
representation `delta` of `GL_r(F)`. These are raw candidates: the structure
has no field asserting that a Speh quotient exists. Its `IsDiscreteSeries`
predicate separately requires irreducibility, unitarizability through an
actual invariant positive definite Hermitian form, and
`T.IsSquareIntegrable delta.representation`. The latter is the published
analytic predicate on the actual quotient by the center, with admissibility,
a unitary scalar central character, and square-integrable absolute smooth
matrix coefficients for all Borel Haar measures. Existence of these measures
is already proved in `Classification.Tempered`.

`d.degree` is exactly `k*r`. `d.exponent i` is
`((k : ℝ)-1)/2-(i : ℕ)` for `i : Fin k`, with real subtraction.
It lists `(k-1)/2, (k-3)/2, ..., -(k-1)/2`; in particular its negative
terms are not truncated natural subtraction.
`d.centeredInduced` uses `BlockShape.uniform k r d.rank_pos`,
the constant family `delta`, and `T.twistedProductInduced` at these
exponents. Thus it is the actual centered decreasing induction on
`GL_(k*r)(F)`, with all `k` factors of the same positive rank `r`.
The construction makes sense for raw candidates; the Speh relation restricts
them to discrete-series data.

The imported normalized product uses the standard upper block parabolic,
the external tensor product of actual block representations, covariance
`f(pg) = delta_P(p)^(1/2) sigma(p) f(g)`, and right translation.
The twist is the published `T.segmentFactor`, through
`T.twistedProductInduced`: `nu(g)=|det(g)|_F`, with residue-normalized
`|varpi|_F=q^(-1)`. These are constructions from
`Classification.LanglandsData`, `Classification.Segments` and
`Induction.BlockFactors`, rather than a newly assumed operation.

## Speh relation and separate statement targets

`d.IsSpeh pi` means that `d.IsDiscreteSeries`, that an actual surjective
equivariant complex-linear map from `d.centeredInduced` to the irreducible
representation `pi` exists, and that every irreducible smooth quotient of
the same standard module is isomorphic to `pi`. The last condition quantifies
over all actual smooth representations in the prescribed carrier universe.
It is uniqueness of the isomorphism class of irreducible quotients; it does
not assert equality of their quotient-map kernels. No representative is
chosen by this definition.

`SpehExistenceUniqueness F T` separately asserts that each discrete-series
datum has such a quotient. Its uniqueness clause is carried by `IsSpeh`.
This is the source assertion immediately before Theorem D on Tadic
1986 p.338 and repeated in §7.4 p.370 and before A.8 p.375.

`SpehLengthOneComparison F T` is an elementary comparison target derived
from these definitions, rather than an additional numbered result in Tadic.
For discrete-series data with `length=1`, and an explicit equality
`h : d.degree = d.rank`, it asserts
`d.IsSpeh pi ↔ Nonempty ((h ▸ pi) ≅ d.delta)`.
The rank equality follows arithmetically from `length=1` and is passed
explicitly to keep the group-index transport visible. A proof needs the
one-block normalized-induction comparison and the zero determinant-twist
comparison, followed by the fact that a surjection between irreducibles
is an isomorphism. No such proof is supplied here.

The decreasing Speh quotient must be distinguished from the special
quotient of an increasing cuspidal segment in the published `Segments`
interface. The latter construction cannot substitute for `centeredInduced`
without a further comparison.

## Actual Tadic building blocks and exhaustion

For a candidate `S` of rank `d.degree`, `d.complementaryInduced S alpha`
is the entire normalized product on `GL_(2*d.degree)(F)` with the
uniform two-block shape, constant family `S`, and exponents
`alpha,-alpha` in that order. Both twists use exactly the same supplied
representation `S`, not independently chosen isomorphic quotients or a
contragredient.

`IsTadicBuildingBlock F T pi` is the disjunction of:

- A datum `d`, an actual `S` satisfying `d.IsSpeh S`, and a rank equality
  `h : d.degree = n`, with an isomorphism `(h ▸ S) ≅ pi`.
- A datum `d`, the same kind of `S`, an exponent `0 < alpha < 1/2`,
  and a rank equality `h : 2*d.degree = n`, with an isomorphism from
  `(h ▸ d.complementaryInduced S alpha)` to `pi`.

The relation is closed under actual isomorphisms because Tadic's original
uses representation classes. In each branch its witnesses retain the
source length, square-integrable rank, Speh candidate and precise total-rank
transport. Both interval endpoints are excluded. No genericity or Hermitian
parameter-matching hypothesis occurs.

`TadicUnitaryDualExhaustion F T` states the existence portion of Tadic
Theorem D(ii), pp.338–339, also §7.5(ii), p.370. For every actual irreducible
unitarizable smooth representation `pi` of `GL_(n+1)(F)`, it gives
`B : BlockShape (n+1)` and actual representations `sigma i` of each
`GL_(B.size i)(F)`, all satisfying `IsTadicBuildingBlock`, together with
an isomorphism from `pi` to the **entire**
`(T.normalizedProductInductionFunctor B).obj sigma`. It is not merely
a quotient or subquotient assertion. `B` supplies positive block ranks
and their sum, hence a finite nonempty family for positive total rank.
No admissibility premise is added to the input representation.

`TadicUnitaryDualStatements F T` conjoins Speh existence/uniqueness,
the elementary length-one comparison and exhaustion.
`PadicTadicUnitaryDualStatements.{uF,uV}` quantifies this interface over
every prime, finite p-adic extension and compatible topology.
The pair does not state the construction direction D(i) or the unordered
uniqueness portion of D(ii). It does not import, assume, or prove the
final `UnitaryGenericExhaustion` proposition.

## Original source and proof boundaries

The retained original is Marko Tadic, *Classification of unitary
representations in irreducible representations of general linear group
(non-archimedean case)*, Ann. Sci. ENS (4) 19 (1986), 335–382.
It is registered as `tadic-1986-unitary`, at
`/home/taskhub/central-library/Tadic--Classification of unitary representations in irreducible representations of GL(n)--1986.pdf`,
SHA-256
`08e4e1e7c1ccc1e340999287867bc0448f3d8f4bab49906fbf1deda866ae4683`.
Read printed pp.337–339, §7.4–§7.5 p.370 and Appendix pp.371–380;
visually checked the centered quotient formula and both building-block
types on p.338. PDF page numbers are printed page minus 333, one-based.
No source-specific errata note was present in the supplied Library.

The p.339 caveat is material: the main §§7–8 argument uses preservation
of irreducibles by the Zelevinsky involution, for which the author then had
no written proof in full generality. The Appendix supplies a
characteristic-zero route without assuming that general involution
assertion; it applies to the finite p-adic extensions here.
A.8, pp.375–377, obtains Speh unitarizability from globalization and
residual automorphic spectrum inputs, citing [3] or [22] and [16].
A.10–A.11, pp.377–379, give the resulting characteristic-zero
classification route; A.12 p.380 records alternatives and dependencies.
The cited upstream originals are not claimed to have been read or proved
by this pair.

Outstanding proof obligations include the actual Speh quotient
existence/uniqueness and length-one comparisons; analytic classification
and complementary-series inputs; comparison of the source's analytic
representations and square-integrability conventions with the published
smooth predicates; Haar-measure normalization independence; and the
finite-product, block-reordering and rank-transport comparisons.
For a later unitary-generic application, generic Speh elimination
(`k=1`), genericity reflection through products, flattening complementary
pairs, and the resulting parameter symmetry are separate obligations.
None is encoded as a hypothesis that already implies this exhaustion.
