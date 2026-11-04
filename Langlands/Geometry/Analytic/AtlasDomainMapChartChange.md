# Universal bounded chart change for local full domains

This internal construction connects the already constructed domain restrictions
to general bounded chart change on the same presented affinoid coefficient
algebra. It assumes an arbitrary indexed affinoid atlas, with no saturation or
directedness hypothesis.

For a full domain `U` in original chart `i`, whose ambient image lies in original
chart `j`, `domainChartRestriction_eq_changeMapChart` identifies the complete
bounded map `domainChartRestriction i j U` with `changeMapChart` applied to the
original structural map `U.baseMap`. The proof uses the actual finite common-chart
cover of `U`. On each member, the structural equations of its two domain
inclusions supply a factorization test for general chart change. The result is
the defining local equation of the domain restriction. Finite-cover separation
of algebra elements proves equality of bounded maps, including on nonreduced
algebras.

`domainChartRestriction_isMapChartChange` therefore supplies the full universal
law: after every bounded map from `U.algebra` to any presented affinoid algebra,
every factorization through a common original subchart gives the prescribed
restriction formula. Coefficient maps need not be domain inclusions.

`changeDomainChartRestriction` constructs a second target-chart change on
`U.algebra`. Its equality theorem proves that it recovers the direct domain
restriction to the final containing chart. The pair theorem gives full
`IsMapChartChange` compatibility between restrictions from any two containing
original charts. Finally, `domainRestriction_isMapChartChange` applies the same
law to the parent-chart structural maps associated with every constructed
inclusion of local full domains.

The provenance is internal: finite domain-cover gluing and its exact local
equations, the universal law for general chart change, and its proved
transitivity. This unit does not construct extension of a general strong atlas
map or assert that all original strong-map families satisfy intrinsic coherence.
