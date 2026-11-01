# Actual adelic block parabolics

Author: Worker 2.

This internal construction specializes the published `BlockShape` parabolic
and Levi groups to the actual number-field adele rings and restricts the
published `AdelicGL` finite/infinite splitting to them. The field `F` has any
universe `uF`, with `Field F` and `NumberField F`. The total rank is any natural
number, and `B : BlockShape n` supplies positive ordered block sizes summing to
that rank. The empty shape at rank zero is allowed.

`Rational`, `Full`, `Finite` and `Infinite` are the actual upper block
parabolic subgroups over `F`, its full adele ring, its finite restricted-product
adele ring and its product of archimedean completions, respectively. The
adelic groups carry the subgroup topologies from matrix units, which retain
both matrix and inverse coordinates. No topology is selected on `F`.

`rational` restricts the actual entrywise diagonal map to the parabolic;
zero entries remain zero under the algebra map. Its injectivity follows from
the published injectivity on actual general linear groups.

`infinite` and `finite` are continuous homomorphisms obtained by restricting the
actual coefficient projections. Membership follows by applying the coefficient
projection to every entry below the block diagonal. `pair` pairs the matrices
and their inverses with the published `AdelicGL.pair`; the two component zero
conditions establish parabolic membership. The three inverse identities prove
`split`, a genuine multiplicative homeomorphism between the full parabolic and
the product of its archimedean and finite factors. Continuity follows from the
ambient maps and the subgroup topology. `ofInfinite` and `ofFinite` include one
factor with the other factor equal to the identity.

`FullLevi`, `FiniteLevi` and `InfiniteLevi` are the actual products of general
linear groups of the respective block sizes over these coefficient rings.
`leviInfinite`, `leviFinite`, `leviPair` and `leviSplit` apply the actual general
linear group splitting to every block. Product continuity and the blockwise
inverse laws give a multiplicative homeomorphism for the Levi products.

The Levi projection commutes with finite and archimedean projection and with
pairing: these identities are proved on the actual entries extracted from each
diagonal block. The block diagonal section also commutes with both projections.
The proof compares arbitrary entries by the block index equivalence; a
same-block entry is preserved and an entry between different blocks is zero.
`split_leviProjection` and `split_leviInParabolic` state the resulting commuting
diagrams for the two actual multiplicative homeomorphisms.

The generic Levi embedding, projection, continuous section, closedness and
unipotent/Levi factorization already belong to
`Langlands/Group/GL/Blocks`; they are reused without replacing that branch.
This unit introduces no modulus formula, normalized global induction,
isobaric representation or automorphic existence result.

Provenance is internal: the constructions are restrictions and products of the
published actual maps in `Langlands/Global/AdelicGL` and specializations of the
published arbitrary-ring block constructions in `Langlands/Group/GL/Blocks`.
It makes no new claim of identification with original literature.
