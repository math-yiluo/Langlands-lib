# Reduction of finite-length twisted distributions to irreducibles

A Noetherian semisimple representation is a finite internal direct sum of
irreducible subrepresentations. Use their inclusions and projections to
resolve the identity. The finite-rank trace of the integrated action composed
with a twisting map is the sum of the traces of its diagonal components.

Each diagonal component is an intertwining map from the corresponding
irreducible subrepresentation to its pullback by the automorphism. The
pullback is irreducible, so a nonzero component is an isomorphism. A zero
component has zero trace. Thus `twistedDistribution_mem_of_semisimple` puts
the twisted distribution in any subspace containing the twisted
distributions of the irreducible subrepresentations.

`TwistedDistributionConstituentSpanStatement` is the corresponding
assertion for an admissible finite-length representation with a twisting
isomorphism. A subspace that contains all twisted distributions of its
stable irreducible subquotients also contains its twisted distribution.
The proposition uses a left-invariant measure finite on compact subsets,
a fixed carrier universe for the subquotients, and the original operator
on the finite-length representation.

The proof `twistedDistribution_mem_of_finiteLength` works by induction on
the kernels of quotient maps from the original representation, ordered
by reverse inclusion. The Noetherian property makes this order well-founded.
A zero quotient has zero trace. A nonzero quotient has a nonzero semisimple
socle, which the twisting isomorphism preserves. Restrict the isomorphism
to this socle and descend it to the quotient by the socle. The maps give
an exact sequence to which additivity of twisted distributions applies.
The socle trace belongs to the subspace by the semisimple calculation.
Its irreducible subrepresentations embed in a quotient of the original
representation, so they are among the original subquotients. The trace
on the quotient by the socle belongs to the subspace by induction, since
the kernel has strictly increased.

This distribution-space result uses the exact sequences of twisted pairs
in Henniart–Lemaire (2011), II.5.2, and the trace relation in II.5.4,
Remarque. The proof uses the Library's actual smooth subquotients, socle
and finite-rank trace.
