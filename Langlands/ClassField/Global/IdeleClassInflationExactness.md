# Conditional inflation–restriction for actual idele-class cohomology

This derived supporting module compares the abstract inflation–restriction
sequence with the published maps on actual idele-class cohomology in a
compatible tower of number fields `F → E → L`, with `E/F` and `L/F` Galois.
All three fields lie in an arbitrary common universe.

The main result `ideleClassH2InflationExactness_of` assumes the published
proposition `IdeleClassGaloisDescent` at this universe and that
`relativeIdeleClassCohomology E L 1` is a subsingleton. It proves that
`relativeIdeleClassInflation F E L 2` is injective and that its linear-map
range equals the kernel of `relativeIdeleClassRestriction F E L 2`.
The two arithmetic inputs remain explicit hypotheses. This module proves
neither of them and does not prove `GlobalInvariantStatement`.

## Coefficient and cohomology comparisons

Let `S` be the kernel of `Gal(L/F) → Gal(E/F)`. The module reuses
`towerRestrictionKernel`, `towerRestrictionKernelEquiv` and
`towerQuotientEquiv` from the published local `FiniteTowerCohomology` module.
These are field-theoretic constructions: they identify `S` with `Gal(L/E)`
and `Gal(L/F)/S` with `Gal(E/F)`.

`ideleClassTowerInvariants` is the submodule of the actual additive idele
classes of `L` fixed by `S`. `ideleClassTowerInvariantInclusion` corestricts
the published idele-class inclusion to this submodule. Equivariance of that
inclusion proves that it takes values in the invariants. Galois descent
then proves injectivity and surjectivity of this map, giving
`ideleClassTowerInvariantsEquiv`. Surjectivity uses the kernel group
equivalence to turn invariance under `S` into fixedness under `Gal(L/E)`.
The inclusion's original equivariance also proves that this linear
equivalence intertwines the quotient action.

`ideleClassTowerQuotientCohomologyIso` applies the group-cohomology map
isomorphism to these group and coefficient equivalences, in every degree.
Its inflation comparison shows that composing abstract inflation with
the inverse comparison gives precisely the published
`relativeIdeleClassInflation`, including its actual coefficient inclusion.

`ideleClassTowerKernelCohomologyIso` uses the kernel group equivalence
and the identity on idele classes. Its restriction comparison gives
precisely `relativeIdeleClassRestriction`, with identity coefficients.
These kernel comparisons do not need the descent hypothesis.

## Exactness proof and provenance

The kernel comparison transports the supplied upper relative `H¹`
vanishing to the normal subgroup. The published theorem
`Langlands.Cohomology.h2InflationRestrictionExactness` now gives injectivity
and the range-kernel equality for abstract inflation and restriction.
The two comparison equations transport this conclusion to the actual
maps. The quotient comparison is bijective, so precomposition preserves
the inflation range and injectivity; the kernel comparison is injective,
so postcomposition preserves the restriction kernel.

The implementation follows the already published local
`RelativeH2InflationProof` and `FiniteTowerCohomology` construction, replacing
units by the actual idele classes and explicitly assuming their Galois
descent and upper `H¹` vanishing. It reuses those modules' field group
equivalences unchanged. This is an internal derivation from the cited
Library modules, with no new arithmetic axiom, substitute coefficient
model, or asserted global invariant.
