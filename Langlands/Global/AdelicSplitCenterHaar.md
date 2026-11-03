# Haar measure and exact normalization of actual adelic factors

Let `F` be a number field and `T` an actual commutative group scheme over `F`,
with a supplied isomorphism to the split torus indexed by a finite type `I`.
The positive subgroup in this file is the existing `intrinsicSubgroup F T`
inside the actual full adelic points of `T`. The finite type may be empty.

`positiveLogCoordinateEquiv` composes the existing `positiveLogEquiv` with
`dualCoordinatesContinuousEquiv`. It is a continuous group equivalence from
that actual positive subgroup to `Multiplicative (I → ℝ)`. Its coordinates
are evaluations of the normalized character logarithm at the genuine coordinate
characters. In particular, it retains the number-field degree normalization
already implemented in `PositiveRealTorusLog`. Its inverse first applies
the inverse real-dual coordinate equivalence to the real vector, then applies
the existing positive exponential to the resulting character functional.

`logCoordinateMeasurableSpace` and `logCoordinateBorelSpace` give these real
coordinates their Borel sigma algebra. The actual positive subgroup retains
the inherited measurable structure from the existing Borel sigma algebra on
adelic points. Its topology and carrier are unchanged.
`positiveIsTopologicalGroup`, `positiveLocallyCompactSpace` and
`positiveSecondCountableTopology` derive their properties from the coordinate
equivalence. These assertions require the supplied finite splitting but do
not require affinity or finite type of an ambient group scheme.

`positiveHaarMeasure` pushes the chosen Mathlib `Measure.haar` on the finite
real coordinate group through the inverse coordinate equivalence. It is a
Haar measure on the actual positive subgroup, is sigma finite and regular,
and is right invariant. Haar transport proves the first assertion; local
compactness and second countability give sigma finiteness; homeomorphic
transport proves regularity; the commutative real coordinate group supplies
right invariance. This initial choice is not asserted to be a particular
Lebesgue normalization or to be independent of the supplied splitting.

Now let `G` be an actual affine locally finite type group scheme over `F`
and `i : T.toGrp ⟶ G` an actual homomorphism. Retain injectivity of
`characterRestrict i` and finite index of its range.
`decompositionHaarMeasure` is the pushforward of

```text
positiveHaarMeasure × Measure.haar on normOneSubgroup F G
```

through the existing `normOneDecomposition`. That homeomorphism sends
`(a,n)` to `positivePointMap a * n`; its inverse gives the actual positive
factor and norm-one factor. The norm-one measure is its own existing Haar
measure, rather than the restriction of ambient Haar.
The definition of the product pushforward needs no centrality assumption.
Under the explicit scheme-theoretic hypothesis `hc : IsCentral i`,
`decompositionHaarMeasure_isHaarMeasure` uses the already proved
`normOneDecompositionMulEquiv`, product Haar invariance and transport through
that genuine group equivalence.

Write `μ₀` for this product pushforward and `μG` for the existing ambient
`Measure.haar`. `decompositionHaarScalar` is precisely Mathlib's
`Measure.haarScalarFactor μ₀ μG`, with its required invariance instances
supplied by the construction. `decompositionHaarScalar_pos` proves `c > 0`
for this scalar `c : ℝ≥0`, and `decompositionHaarMeasure_eq_smul` proves
`μ₀ = c • μG` by Haar uniqueness on the actual locally compact second
countable ambient group.

`normalizedPositiveHaarMeasure` is `c⁻¹ • positiveHaarMeasure`. It remains
Haar, sigma finite, regular and right invariant.
`map_normalizedPositiveHaarMeasure_prod` proves the exact identity

```text
map normOneDecomposition
  (normalizedPositiveHaarMeasure × norm-one Measure.haar)
    = ambient Measure.haar.
```

The proof moves the scalar through the product and pushforward and cancels
`c⁻¹ * c = 1`. Thus the ambient and norm-one Haar choices are held fixed;
only the positive factor is rescaled.
`measurePreserving_normOneDecomposition` and its inverse theorem express
the same exact normalization in both directions.

For every complex-valued function on the actual ambient group,
`integrable_normOneDecomposition_iff` gives the exact equivalence of
convergence with convergence in these product coordinates.
`integral_normOneDecomposition` separately identifies the total Bochner
integrals, whether or not they converge. The two Fubini theorems require
ambient integrability and give either order of integration over actual
positive and norm-one points. They follow by product Fubini after the exact
measure transport.

`ambientHaar_isMulRightInvariant` explicitly assumes right invariance of
the existing norm-one Haar measure. Right invariance of normalized positive
Haar and of the product, transported through the actual central group
equivalence and the exact normalization, then proves right invariance of
the existing ambient Haar. This conditional implication supplies no proof
of norm-one unimodularity.

This is internally derived content. The actual logarithmic equivalences,
character restriction and central decomposition are imported constructions;
their source interpretations and normalization factors are documented in
`PositiveRealTorusLog`, `CharacterRestrictionRealDual`, `AdelicLogSection`
and `AdelicNormOneDecomposition`. The new measure construction and identities
use Mathlib's existing Haar existence, transport, uniqueness and Fubini
theorems. No external mathematical existence assertion is added here.

The explicit algebraic inputs have not been constructed for every connected
reductive group, nor has the supplied positive torus been identified with
Getz--Hahn's greatest rational split centre. Haar measure on the full
positive-times-principal subgroup and its full-group quotient Weil
compatibility still require a separate product/subgroup argument.
Reduction theory, finite volume and general reductive analytic
unimodularity remain separate obligations.
