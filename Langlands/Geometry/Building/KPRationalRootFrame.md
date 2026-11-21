# Rational coordinates for the §13.4 optimization problem

This module constructs affine coordinates in which every affine root has a
rational constant term and integral linear coefficients. It is a prerequisite
for the rational linear programming argument after Definition 13.4.2 in
Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), printed pp. 472–473
/ PDF pp. 503–504. It does not assert the existence of an optimal point.
The rational-point predicate is the published interpretation of Definition
13.4.1: every affine root has a rational value at the point.

## Data and construction

In `Langlands.Geometry.Building.AffineRootSystem`, `RationalRootFrame Ψ`
consists of an origin `o : A`, a real basis `b` of the translation space `V`
indexed by `Fin (Module.finrank ℝ V)`, a proof that `o` is rational, and proofs
that `ψ.linear (b i)` is an integer for every `ψ ∈ Ψ` and index `i`.
`IsAffineRootSystemWithRankZero.rationalRootFrame` constructs this frame from
the corrected affine-root axioms and a positive rational period `r` of `Ψ`.
The period need not be the least one.

### Rational origin

`IsAffineRootSystemWithRankZero.sub_apply_mem_range_rat_of_linear_eq` shows
that the constant difference `η − ψ` of affine roots with the same
derivative has a rational value at any point `o`. To see this, consider the
additive subgroup of real constants whose translations in both directions
preserve that derivative fibre. This subgroup is not dense: sending such a
translation in `(-1,1)` to the translate of `ψ` injects into a bounded subset
of the fibre, which is finite by AR 4. A dense subgroup would meet the open
interval in a dense subset of the interval, and a finite subset of `ℝ` is
closed. The subgroup is therefore cyclic by Mathlib's
`AddSubgroup.dense_or_cyclic`. It contains `r`; subtraction of `r` follows
from negation of roots and the period axiom, or the integer-shift lemma in
`KPOptimalPoints`. Within this fibre the map `φ ↦ 2ψ − φ` preserves roots:
apply the root reflection in `ψ` (AR 2), then negate. Composing this map
with the analogous map for `η` translates by `2(η − ψ)`; reversing the order
gives the inverse translation. Thus both `r` and `2(η(o)−ψ(o))` are integer
multiples of a single real generator. Since `r` is positive and rational,
`η(o)−ψ(o)` is rational as well.

`IsAffineRootSystemWithRankZero.isRationalPoint_of_isSpecialPoint` applies
this to any special point `o` (Definition 1.3.39(1)). Given `ψ ∈ Ψ`, choose
`η` vanishing at `o` with the same derivative kernel. If `v` is its coroot,
then `ψ − ψ.linear(v) • η` is a root of derivative `−ψ.linear` and value
`ψ(o)` at `o`. For the derivative calculation, the vector
`w − (η.linear(w)/2) • v` is in the common kernel for every `w`. Negating the
reflected root yields a root with the same derivative as `ψ` and value
`−ψ(o)`. The difference of the two values is rational by the fibre result,
so `ψ(o)` is rational. The frame uses the special point supplied by the
published `exists_isSpecialPoint`. This argument does not require the
stronger extra-special condition or a reduced affine root system.

### Integral linear coefficients

The published root pairing of derivatives has the actual space `V` on its
coroot side. The root-system instance in `AffineDerivativeRootPairing`
gives that its coroots span `V`. `Module.Basis.ofSpan` supplies a basis
contained in that set, which the construction reindexes by `Fin`. Every
derivative takes integer values on those vectors by AR 3. This proves the
integrality field of the frame. The argument also admits the empty
root system in rank zero, where the basis has no vectors and root tests are
vacuous.

## Coordinate evaluation and supplied buildings

- `RationalRootFrame.fromCoordinates` is the affine equivalence from real
  coordinate vectors to `A`, using the inverse basis coordinates and then
  translation by the origin.
- `rootConstant` and `rootCoefficient` choose rational values for the
  constant term and the integral coefficients, respectively. The two
  `cast_` lemmas recover their specified real values.
- `apply_fromCoordinates` gives the root's value as the constant term plus
  the sum of each coefficient times the corresponding coordinate.
- `isRationalPoint_fromCoordinates` shows that points obtained from
  rational coordinate vectors satisfy `IsRationalPoint Ψ`. The converse is
  not needed here and is not stated.
- `ValuationBuildingData.rationalRootFrame` uses the published axioms for
  its actual affine roots and the period `2` proved in `KPOptimalPoints`.
  This is a construction on supplied valuation data, in mixed or equal
  characteristic, not a construction of those data.

## Provenance and limits

The affine-root axioms are KP Definition 1.3.1 (printed pp. 14–15 / PDF
pp. 45–46), with the infinite-fibre addition in the authors' 1 November 2024
corrections (PDF p. 2). The Library expresses absence of accumulation in AR 4
as bounded finiteness in each derivative fibre. Special points are Definition
1.3.39(1) (printed p. 29 / PDF p. 60); the book obtains their existence from
Proposition 1.3.43(1)–(2) (printed p. 30 / PDF p. 61). The construction uses
the Library's proof of special-point existence and root-pairing interface,
not an extra-special point theorem. The rational frame, the parallel-fibre
argument and the rationality of the origin are derived here; KP §13.4
instead discusses rationality using simple affine roots. The §13.4 claims
have no entry in the Chapter 13 corrections (PDF p. 49). No comparison
between the generator conventions of §1.3.19 and §13.4, compact optimization
result, or proof of Lemma 13.4.4 is included. No external code is adapted.
