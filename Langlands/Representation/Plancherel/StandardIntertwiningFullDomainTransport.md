# Full-domain transport of the actual standard intertwining integral

This is an internal consequence of the published
`StandardIntertwiningNaturality` and `StandardIntertwiningTargetLaws` modules.
Its hypotheses and conclusion retain independent inducing-carrier universes.

`domain_eq_top_of_equiv` transfers full domain from a representation `A` to an
equivalent representation `B`. For any source vector for `B`, its image under
the inverse induced equivalence belongs to the full domain for `A`.
`inducedEquiv_mem_domain_iff` then puts the original vector in the domain for
`B`. Thus scalar convergence and integral representability are transported in
their actual existing definitions. Applying the argument to an equivalence
and its inverse gives `domain_eq_top_iff_equiv`.

`domain_eq_top_on_unramifiedTwistOrbitSaturation` applies this transfer to
each character in the actual orbit saturation. The published
`mem_unramifiedTwistOrbitSaturation_iff` supplies a character in the original
region and an isomorphism from its twist to the given twist.
`SmoothRep.equivOfIso` supplies the equivariant equivalence used by the transfer.
The reverse restriction uses `subset_unramifiedTwistOrbitSaturation`, giving
`domain_eq_top_on_unramifiedTwistOrbitSaturation_iff`. These conclusions use
no admissibility, finite length, continuity of the indexed positive-character
family, or initial analytic estimate. They preserve the same actual quotient
measure and full-domain predicate.

With the same actual quotient measure, compatible regular right invariant
Haar measures, closed Levi, and squared-modulus compatibility as the published
target operator, `fullSourceIntertwiner_equivalent_representative` returns
the transported full-domain proof and the required equality of actual
intertwining maps. It uses the previous transfer and
`fullSourceIntertwiner_natural`. It assumes full domain for `A` and does not
prove initial convergence, rationality, or squared-modulus compatibility.
