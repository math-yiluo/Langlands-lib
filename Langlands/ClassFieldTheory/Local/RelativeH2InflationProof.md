# Degree-two exactness for finite Galois towers

Author: Worker 58. The proof imports the published generic exactness theorem
by Worker 138 and the published finite-tower comparisons by Worker 58.
Their dependencies retain their authorship in their own paired Markdown.

`Langlands.ClassFieldTheory.Local.finiteRelativeH2InflationExactness` proves
exactly `FiniteRelativeH2InflationExactness.{u}`. For every compatible tower
`K → L → M` of fields in an arbitrary common universe, with `L/K` and `M/K`
finite Galois, inflation
`relativeInflation K L M 2` is injective and its linear range equals the
linear kernel of `relativeRestriction K L M 2`. The cohomology modules
are the actual ordinary group cohomology of the field unit groups, in
additive notation over the published lifted integer ring `IntegerScalars`.
All hypotheses are those of the existing target; the theorem has no outer
premises.

The proof applies
`Langlands.Cohomology.h2InflationRestrictionExactness` to `Gal(M/K)`,
`unitsRepresentation K M`, and `towerRestrictionKernel K L M`, the kernel
of restriction to `Gal(L/K)`. The published
`towerKernelH1_subsingleton K L M` supplies subgroup first-cohomology
vanishing from `finiteRelativeH1Vanishing`, the project's Hilbert 90 proof.
Thus vanishing is proved for these coefficients rather than assumed.

Write `C` for the resulting `groupCohomology.HInfRes` complex in degree two,
`q` for `towerQuotientCohomologyIso K L M 2`, and `e` for
`towerKernelCohomologyIso K L M 2`. The published comparison identities give
`q.inv ≫ C.f = relativeInflation K L M 2` and
`C.g ≫ e.hom = relativeRestriction K L M 2`.
The inverse of `q` is injective and surjective, and `e.hom` is injective.
Composing the generic inflation injection with `q.inv` proves the first
conclusion. For the second, `LinearMap.range_comp_of_range_eq_top` removes
the surjective precomposition by `q.inv`, and
`LinearMap.ker_comp_of_ker_eq_bot` removes the injective postcomposition by
`e.hom`. The required range–kernel equality is then precisely the generic
theorem's second conclusion.

This is the finite-tower specialization of Jean-Pierre Serre, *Local Fields*
(1979), Chapter X, section 4, Proposition 6, printed page 156 / PDF page 162.
It uses Chapter VII, section 6, Proposition 5 in degree two, printed
pages 117–118 / PDF pages 123–124, and multiplicative Hilbert 90 from
Chapter X, section 1, Proposition 2, printed page 150 / PDF page 156.
The registered original is `serre-1979-local-fields`, SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
These passages and the source fingerprint were checked during the
comparison construction. Serre's fields `k ⊆ K ⊆ L` correspond to Lean's
`K → L → M`. The final specialization follows Serre's use of generic
exactness and Hilbert 90; the imported generic theorem uses an internal
explicit-cochain proof, as its own Markdown explains.

The result asserts injectivity and middle exactness, without asserting
surjectivity of restriction. The continuous-cohomology passage to infinite
extensions and local invariant existence are separate results.
