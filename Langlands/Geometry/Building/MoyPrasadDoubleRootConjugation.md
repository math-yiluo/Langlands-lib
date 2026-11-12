# Mixed conjugation from double-root commutator friendliness

This internal derived construction discharges the explicit middle-coordinate bound in `MoyPrasadMixedConjugation` using the published predicate `CentralizerFiltration.IsDoubleRootCommutatorFriendly`. The filtration and its stronger predicate remain supplied data.

`double_opposite_central_mem_of_doubleRootCommutatorFriendly` treats an ordinary element `u` at depth zero and a doubled opposite element `v` at depth `r > 0`. V4 puts `v` at ordinary opposite depth at least `r/2`. For nontrivial inputs their finite ordinary valuations `t, s` therefore satisfy `t ≥ 0` and `s ≥ r/2`. An actual decomposition `u v = v' j(z) u'` gives the commutator decomposition

`v⁻¹ u v u⁻¹ = (v⁻¹ v') j(z) (u' u⁻¹)`.

The double-root predicate puts this same `z` in filtration depth `2(t+s)`. Antitonicity places it in depth `r`. If either input is the identity, injectivity of the actual opposite-root/centralizer/root product forces `j(z) = 1`, and monicity of the actual centralizer inclusion gives `z = 1`. This first theorem needs the stronger predicate and the original valuation data, but no apartment axioms or other filtration predicates.

`conjugate_double_opposite_mem_moyPrasad_of_doubleRootCommutatorFriendly` combines that estimate with the two root-coordinate bounds already proved in `MoyPrasadMixedConjugation`. It yields membership of the literal conjugate in the original depth subgroup, with both original factors of each root block retained.

`sharpFixer_le_normalizer_moyPrasad_of_doubleRootCommutatorFriendly` feeds this mixed bound into the published all-root normalization reduction. The other root pairs, conjugation of the centralizer image and depth zero are exactly the cases proved there. `isMoyPrasadAt_unique_of_doubleRootCommutatorFriendly` then uses normalizer stability and the actual quotient relation to identify any two original reduced-building presentations. `moyPrasadAtUniqueOfDoubleRootCommutatorFriendly` chooses such a subgroup with its presentation and uniqueness proof.

The results apply in arbitrary universe to supplied apartment data and a supplied filtration with the stated properties. They do not prove existence of a filtration satisfying the stronger predicate, the original covariance target without that premise, the commutator target, or the host simultaneous-basis theorem. Their provenance is composition of the published mixed-coordinate and covariance reductions with the published double-root predicate; no new translation of an external source is claimed.
