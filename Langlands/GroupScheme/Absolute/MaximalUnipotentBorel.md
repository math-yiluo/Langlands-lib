# Maximal unipotent subgroups and Borel unipotent parts

`IsBorelUnipotentSubgroup i` says that there is an actual Borel embedding
`b : B ⟶ G` and a greatest unipotent subgroup `u : U ⟶ B` such that
`u ≫ b = i`. Its equivalence with `IsMaximalUnipotentSubgroup i` is
Milne 2017, Proposition 17.14 (printed p.356). The equivalence and conjugacy
theorem assume an algebraically closed field and a smooth connected affine
ambient group. The maximal-unipotent predicate means maximal among smooth
connected unipotent closed subgroups.

For the forward direction, the given unipotent subgroup is solvable by the
published coefficient-representation argument. The published solvable-subgroup
Borel containment theorem places it inside a Borel. A unipotent part of that
Borel contains the given subgroup on every test scheme. The induced
factorization is an isomorphism by maximality, so the original subgroup is
itself the unipotent part of the Borel.

For conjugacy of two maximal unipotent embeddings, apply the forward direction
to each. The published Borel conjugacy theorem identifies their Borels after
conjugation by a rational point. The greatest-unipotent-part predicate
transports under the resulting isomorphism. Uniqueness of unipotent parts
then gives the actual source isomorphism and its conjugacy equation.

For the reverse direction, finite coordinate-kernel height supplies one
maximal smooth connected unipotent subgroup. By the forward direction it is
the unipotent part of some Borel. Conjugacy of that Borel with the prescribed
Borel, followed by uniqueness of unipotent parts, transports maximality to the
prescribed unipotent part. This proof avoids a dimension comparison.

These arguments use only the foundational maximal-unipotent and greatest-part
helpers and the already published solvable and Borel results. They do not use
quotient image preservation or any clause of the quotient-image target.

Source: James S. Milne, *Algebraic Groups* (2017), source ID
`milne-2017-algebraic-groups`, SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`,
Proposition 17.14 (printed p.356), with Theorem 17.9 for Borel conjugacy
and Theorem 16.33 for solvable unipotent parts. The official errata snapshot
of 2026-11-02 has no correction to Proposition 17.14.
