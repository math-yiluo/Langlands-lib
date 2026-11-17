# The identity locus of a finite-character grouplike family

This is an internal algebraic consequence of the published `Grouplike` and
`CharacterTwist` constructions. It applies to every finitely generated abelian
character group, including groups with torsion.

`HasIdempotentIdentityLocus` is the predicate that one idempotent detects
identity specialization after every coefficient algebra map.

A grouplike element is a chosen monomial if and only if its coefficient at that
degree is one. Orthogonality forces every other coefficient to vanish. The same
criterion after a coefficient map detects equality with that monomial.

For a grouplike homomorphism on a finitely generated character group, choose
finitely many group generators and multiply the coefficient at each generator's
own degree. This product is an idempotent. After any algebra map, the
homomorphism becomes the universal monomial homomorphism precisely when the
product maps to one. One implication uses equality on the generating set. For
the other, a product equal to one makes each factor a unit, and an idempotent
unit is one.

The theorem supplies an algebraic description of the identity locus. It does
not itself assert representability or openness of a group-scheme centralizer.
