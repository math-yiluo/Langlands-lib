# Elementary structural and representative-transport proofs

`parabolicIntertwiningElementaryStatement` proves the entire unapplied
`ParabolicIntertwiningElementaryStatement` at independent universes `u,uV,uW`.
This proof groups the small structural and formal prerequisites of the
conditional finite-length theorem. It does not prove analytic convergence,
rational continuation, or squared-modulus compatibility.

The first conjunct uses `parabolicRadical_isUnimodular`. The supplied
geometric radical is identified with the actual dynamic identity-limit
group by `ParabolicRootPresentation.range_comp_radical_eq`. After closedness
is transported along that equality, the published
`Aubert.General.DynamicNormalization.dynamicUnipotent_isUnimodular`
discharges the inner Haar-modulus assertion. Ambient smoothness is taken from
connected reductivity. See `ParabolicRadicalUnimodularity` for the implementation.

The second conjunct is `StandardIntertwining.domain_eq_top_iff_equiv`.
It applies `inducedEquiv_mem_domain_iff` to the inverse equivalence and the
full-domain membership of each inverse image, then repeats in the other
direction.

The third conjunct uses
`StandardIntertwining.fullSourceIntertwiner_equivalent_representative`.
This obtains the second full-domain proof by the same transfer and applies
the published `fullSourceIntertwiner_natural` with both proofs. The equality
uses the existing actual quotient integrals and their original-carrier
representability; no new integral or carrier is substituted. See
`StandardIntertwiningFullDomainTransport` for both implementations.
