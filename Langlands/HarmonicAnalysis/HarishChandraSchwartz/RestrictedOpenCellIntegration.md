# Global open-cell integration with restricted right invariance

This internal measure construction extends the published local range argument
in `RestrictedOpenCellGamma` to global integration when the same cell is
conull. It supplies a consumer for a separately proved conullness theorem.
It does not prove conullness.

## Data and measure construction

Let `G` be a topological group with its Borel measurable structure, and let
`P` and `V` be subgroups with locally compact, second countable subspace
topologies. Supply left Haar measures `mu`, `muP` and `muV` on `G`, `P` and
`V`. No right-invariance instance on the ambient measure is required.

`openCellProductPushforward muP muV` is the pushforward of the actual
product measure `muP.prod muV` through the existing coordinates
`openCellMap (p,v) = p * v^(-1)`. The definition chooses neither a scalar
nor a new subgroup measure.

The three theorems assume that these coordinates form an open embedding
and that their range has `mu`-null complement. Their right-invariance
premise is precisely that every right translation by an element of `V`
preserves `mu`. For normalization, the last two also take a measurable
subgroup `K` with nonzero finite `mu`-mass. Compactness or an Iwasawa
factorization is not needed at this abstract step.

## Implemented argument

`exists_lintegral_openCellMap_of_rightInvariantOn` imports the local range
formula from `RestrictedOpenCellGamma`. Conullness identifies restriction
of `mu` to the range with `mu`, giving a positive finite real coefficient
for the global nonnegative integral formula.

`lintegral_eq_openCellConstant_inv_mul_of_rightInvariantOn` integrates
the indicator of `K` using the existing
`measure_eq_mul_openCellConstant` theorem. If the coefficient is `c` and
the existing double-indicator constant is `gamma`, this gives
`mu(K) = c * gamma`. The positive coefficient and nonzero finite mass of
`K` show that `gamma` is nonzero and finite. Cancellation identifies
`c = mu(K) * gamma^(-1)`, so every measurable nonnegative function obeys
the global iterated integral formula with this exact coefficient.

`measure_eq_openCellConstant_inv_smul_of_rightInvariantOn` then uses
measure extensionality against measurable nonnegative functions,
pushforward integration and Tonelli's theorem to prove

`mu = (mu(K) * gamma^(-1)) • openCellProductPushforward muP muV`.

Thus the construction is an equality of measures as well as a formula
for nonnegative integrals. The scalar is determined by the original
gamma, not supplied as independent normalization data.

## Source and scope

The source context is Waldspurger, *La formule de Plancherel pour les
groupes p-adiques (d'après Harish-Chandra)* (2003), I.1, second formula
(2) and the following gamma display, printed p.240 / PDF p.6; registered
source `waldspurger-2003-plancherel`, SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.
With the source's common-compact normalization `mu(K) = 1`, the coefficient
is gamma inverse. The existing semidirect and source-Haar modules are
responsible for identifying `muP` with the source's weighted `U,M` measure
and gamma with its modulus integral.

This is a derived abstract extension of the published local proof,
rather than a separately numbered result in the source. It retains
conullness as an explicit analytic premise. Actual dynamic-subgroup
realization, special-compact and source normalizations, independence for
different parabolics with the same Levi, Bochner integration and the
Plancherel conclusions require their own comparisons and proofs.
