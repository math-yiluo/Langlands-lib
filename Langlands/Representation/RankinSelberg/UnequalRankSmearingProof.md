# Small normalized cutoffs for JPSS block transfer

Author: Worker 180.

This module supplies the small-cutoff lemmas used by
[UnequalRankBlockSpanProof](UnequalRankBlockSpanProof.md), together with a
generic conditional Fourier-cutoff reduction. These are internal consequences
of local compactness, total disconnectedness, smoothness, and a supplied
Fourier pair. The adjacent-span theorem is in the companion module.

## Normalized small cutoffs

`Smearing.exists_normalized_schwartz_in_open` works on a locally compact
Hausdorff totally disconnected space with a measure finite on compact sets
and positive on nonempty open sets. Inside a given open neighborhood, choose
a compact neighborhood, then a clopen neighborhood inside its interior.
The latter is compact and has finite positive mass. Multiplying its
characteristic function by the inverse complex mass gives a Schwartz
function of integral one supported in the original open set.

`Smearing.exists_normalized_coefficient_cutoff` applies this construction to
a smooth coefficient and a continuous group map `U` taking a chosen point
to the identity. Smoothness supplies an open subgroup fixing the coefficient
in its coefficient model. Pulling this subgroup back by `U` gives an open
neighborhood. The normalized cutoff is supported on parameters whose right
translations fix the coefficient at every group element.
Both results use the actual supplied measure, with no Haar normalization
change or topology on the representation carrier.

## Conditional Fourier cutoff

The finite algebraic averaging lemmas are imported from the published
[UnequalRankSmearingAverage](UnequalRankSmearingAverage.md), without duplicate
declarations. They construct vectors in the original algebraic carrier using
finite scalar simple-function integrals and give integrability and a global
scalar formula for every group point. No completeness of the carrier is
required.

`Smearing.exists_coefficient_cutoff` takes an arbitrary family of group
points `B(i)` and row vectors `x(i)`. Its explicit hypothesis is the
right-translation character identity

```text
f(B(i) U(z)) = ψ(rowPairing z (x(i))) f(B(i)).
```

For a supplied genuine pair `IsRowFourierPair ψ ν κ Φ`, the imported
average has value `Φ(x(i)) f(B(i))`: substitute the character identity
inside the scalar integral, commute the complex factors, take out the
constant coefficient value, and apply the pointwise Fourier equality.
The conclusion retains the global averaging formula for the same coefficient.
This helper remains conditional on its displayed character identity and
Fourier pair; it asserts no independent Fourier-existence theorem.

The actual JPSS upper-column identity and its supplied-pair cutoff are proved
in the separate published `UnequalRankSmearingConjugation` and
`UnequalRankFourierSmearingProof` modules. The companion adjacent-span proof
uses that actual smearing theorem and obtains its pair from the published
`padicRowFourierSurjectivity`, for the actual supplied Haar.

## Provenance

JPSS (1983), printed pp.394–395, and JPS (1979), *Automorphic Forms on GL(3)
I*, Proposition 4.1.4 and Lemma 4.1.5, printed pp.188–190, motivate the
compact-open averaging and Fourier-smearing steps. Their retained originals
were read for the companion proof. The normalized neighborhood construction
and the generic family reduction above are internal implementations of those
steps, with exactly the displayed abstract hypotheses. No adjacent-span or
functional-equation conclusion is used as a premise.
