# Actual constant-term decay from the three analytic prerequisites

The Prop-valued statement
`RationalConstantTermAnalyticReductionStatement.{u}` is proved by
`rationalConstantTermAnalyticReduction`, at arbitrary universe `u`. Its
whole content is the implication

```
RationalXiGlobalUpperBoundStatement ->
RationalUnipotentWeightIntegrabilityStatement ->
RationalLeviXiLowerBoundStatement ->
RationalConstantTermEstimateStatement.
```

The three analytic estimates are explicit premises of this intermediate
reduction. None is proved here. The final target and its existing premises
are unchanged; the module does not prove the final target unconditionally.

The implementation introduces exactly the data of the original actual
constant-term target. It reverses the generic cocharacter and negates the
standard face, retaining the same structural compact `K0`, simultaneous
basis and both Cartan coverings through the proved structural reversal.
The same Iwasawa compact `K` remains valid after reversal, both in the
ambient group and in the Levi, and both actual Xi functions are exactly
preserved. The original supplied Levi Iwasawa decomposition remains an
assumption of the target, rather than being inferred from the ambient one.

The reversed Levi cover supplies finitely many centralizer translates of
the reversed full Levi torus chamber. Exact equality of the actual Levi
subgroups reads this as a double-coset cover of the original Levi with
its original compact intersection. All analytic estimates are first
assembled on this common representative set.

The global Xi premise is applied to the reversed minimal data. Every
representative is a centralizer point times a torus point and hence lies
in the reversed minimal parabolic. Iwasawa covariance therefore separates
its weight from the integrated unipotent weight, giving the abstract
`UnipotentXiBound` for the original ambient Xi. The reversed Levi lower
premise gives `XiLowerBound` on the same representatives; exact Levi Xi
reversal identifies its right side with the target's original Levi Xi.

For weighted integrability, the proof chooses an original standard
cocharacter `zeta` and negates it. The helper
`oppositeUnipotent_neg_standard_eq` proves literal equality of the opposite
radical for `-zeta` with the original integrated standard radical. It uses
the published standard-cocharacter dynamic identification and involutivity
of the inverse cocharacter. Rewriting the reversed integrability premise
by that equality allows the target's given Haar measure to be supplied
directly, with no normalization or measure comparison constant.

The auxiliary scalar modulus condition follows from the proved exact
identity that the reversed ambient minimal modulus times the original
radical modulus equals the reversed minimal Levi modulus. The proof uses
factorization independence of both Iwasawa weights at the representative
and multiplicativity of the nonnegative square root. This supplies the
correct original normalization `sqrt(delta_UJ)` in the target, despite
using opposite minimal data in the analytic estimates.

The published actual product-height bound supplies the remaining scalar
input. `constantTermRepresentativeEstimate_of_bounds` then gives the
normalized integral estimate on the representative set for every real
target exponent. The already published
`rationalConstantTermEstimate_of_compact_doubleCosetCover` extends it to
all actual Levi points by compact-uniform bounds on the weighted kernels.
This step allows `K0`, `K`, and the matrix-height stabilizer to differ;
it requires no exact height or Xi invariance under `K0`.

The main proof has a finite local heartbeat allowance because equality
transport of the actual subgroup, measure and character expressions is
large. There are no additional mathematical hypotheses in that allowance.

Provenance is the derived assembly of the named Library interfaces and
the implemented scalar argument in Waldspurger's Proposition II.4.5,
printed pp.262-263, with the change of minimal parabolic allowed by its
following remark on p.263. Source: Waldspurger (2003), registered as
`waldspurger-2003-plancherel`, SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.
The module deliberately retains the three analytic estimates as premises
of this intermediate proposition. Two of them are proved in the Library
(`rationalXiGlobalUpperBound`, `rationalLeviXiLowerBound`); with a proof of
`RationalUnipotentWeightIntegrabilityStatement` the reduction gives
`RationalConstantTermEstimateStatement` unconditionally.
