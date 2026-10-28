# Actual coefficient recasting for the intermediate tail comparison

Internal supporting constructions by Worker 318 for the comparison motivated by
JPSS section 9.3, printed 456–457.
The actual standard matrix character of `ψ.scale (-1)` equals the inverse
matrix character of `ψ`. Its inverse matrix character equals the standard
matrix character of `ψ`. The module reuses these published equalities.

Four constructions retain the exact underlying function while changing its
type along the corresponding character equality. An actual inverse coefficient
at `ψ` becomes a standard coefficient at `ψ.scale (-1)`. In the other direction,
a standard coefficient at `ψ.scale (-1)` becomes an inverse coefficient at `ψ`;
an inverse coefficient at `ψ.scale (-1)` becomes a standard coefficient at `ψ`.
Conversely, a standard coefficient at `ψ` becomes an inverse coefficient at
`ψ.scale (-1)`.
Each coefficient-image membership theorem transports the actual functional
with `functionalsCongr` and keeps the representing vector. No conjugation,
new representation, or unspecified function-space identification occurs.
These recastings are separate from the integral character-change construction,
which translates the coefficient functions and proves the equality of the
actual rational-value sets.

The numerical rank adapters `whittakerRankCast` and
`inverseWhittakerRankCast` transport standard and inverse coefficients along
an equality of rank indices. Their evaluation theorems identify the transported
functions with evaluation after the explicit numerical matrix reindexing. Their
membership theorems transport the representation by that same equality and
retain actual coefficient-image membership. The smoothness adapter likewise
transports a supplied smoothness proof by equality. These are equality
transports only. The standard `whittakerRankCast` definition and its evaluation
theorem now live in the imported [WhittakerRankCast](WhittakerRankCast.md) pair,
with their original namespace and meaning. This module retains the inverse
cast, both coefficient-image membership lemmas and the smoothness adapter.

An additional identity identifies the actual zero-row unequal-rank tail
function at `ψ.scale (-1)` with the product used in the lower-block
calculation. It uses the original inverse test coefficient as the larger
standard coefficient and the original standard tail coefficient as the
smaller inverse coefficient. Both underlying functions are retained exactly.
The proof unfolds the actual unequal-rank function and uses its proved
zero-row matrix formula. This is a pointwise function identity, with no
measure identification or integration claim.

The final lemma applies the published closed theorem
`zeroRowLastRowCutoff` to the same inverse coefficient recast at
`ψ.scale (-1)` and returns the same zero-or-one Schwartz function. It retains
the supplied p-adic topological realization and only assumes smoothness of
the representation and membership in its actual inverse coefficient image.
It adds no Whittaker-type, irreducibility, functional nonvanishing or measure
assumptions. The separate cutoff proof has been independently accepted and
published; this module imports `ZeroRowLastRowCutoffProof`. It does not prove
the intermediate-tail span inclusion.

Provenance is internal derivation from the published character equalities,
coefficient-image definitions and the published cutoff theorem. The motivating
original is the registered `jpss-1983-rankin-selberg`,
`/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Rankin-Selberg Convolutions--1983.pdf`,
SHA-256 `d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
