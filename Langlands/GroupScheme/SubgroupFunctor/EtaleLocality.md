# Etale locality of represented subgroup membership

This internal module expresses members and maps of an arbitrary etale cover of
a relative test scheme over the original base. A point of a group scheme belongs
to the range of a monomorphic group-scheme homomorphism if and only if it does
on every member of such a cover.

The proof uses Mathlib's subcanonicity of the fppf topology and the published
comparison from the etale precoverage to the fppf precoverage. Every representable
presheaf is therefore a sheaf on the given covering family, so that family is
effective epimorphic. Local lifts of the point agree on every relation because
the subgroup inclusion is monic; the effective epimorphism property glues those
lifts to a global factorization. This is a derived categorical locality lemma;
it has no additional geometric source assertion.

Containment in a monomorphically represented subgroup, and equality of two
such subgroup functors, can consequently be checked after base change along
an arbitrary etale covering family of the base. To prove containment, pull
the cover back to any relative test scheme and translate the local membership
through `baseChangePointsEquiv`. The membership lemma then gives the original
factorization. Equality follows from the two containments. The final
`eq_iff_isRepresentedBy_baseChange_etaleCover` packages the equality criterion
for subgroup functors with explicit monomorphic representatives.

The base scheme and the covering index have independent universes; no
finiteness or quasi-compactness hypothesis on the covering family is imposed.
Monicity, rather than closedness or smoothness, is the hypothesis used for
uniqueness of the local lifts.

## Same-universe sieve formulation

# Detecting represented subgroup containment on an étale cover

This internal lemma supports the intersection step in the opposite Borel proof.
For any subgroup functor and any monomorphic group scheme inclusion, containment
in its image is equivalent to containment after base change to every member of
a jointly surjective étale cover of the base. No closedness of the target
inclusion or representability of the first subgroup is assumed.

One direction is immediate from the definition of subgroup base change. For
the converse, pull the cover back to an arbitrary test scheme. The assumed
local containments give local factorizations of the test point through the
target monomorphism. The absolute image sieve is closed for the fppf topology
by subcanonicity, so these local factorizations give the desired global
factorization. This is a derived categorical argument using the definitions
and the proved `EtaleDescent` support module.
