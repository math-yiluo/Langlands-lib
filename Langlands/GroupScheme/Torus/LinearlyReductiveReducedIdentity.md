# The reduced identity component of a linearly reductive group

`isTorus_reduced_identityComponent_of_linearlyReductive` applies to affine
algebraic group schemes over an algebraically closed field of nonzero
characteristic. If every finite coordinate representation is semisimple in
the all-test sense, the reduction of the actual identity component is a torus.
The ambient group may be nonreduced and disconnected.

The reduction is smooth over the algebraically closed field and has the same
underlying topology as the identity component. Its inclusion into the ambient
group is a composite of closed immersions. For any smooth connected closed
unipotent subgroup of the reduction, composition gives a connected closed
unipotent subgroup of the original group. The published linear-reductivity
obstruction makes every point of this subgroup the identity on every test
scheme. Its range in the reduction is therefore trivial. The published torus
criterion for smooth connected groups now applies.

This derived step combines the unipotent obstruction from Demazure–Gabriel,
*Groupes algébriques I* (1970), IV §3, 3.6, printed p. 510, with Milne,
*Algebraic Groups*, corrected reprint (2022), Corollary 17.25, printed p. 360.

`LinearlyReductiveReducedIdentityStatement` records the induction base for
Nagata's theorem. For a reduced ambient affine algebraic group over an
algebraically closed field of characteristic `p > 1`, its actual identity
component is of multiplicative type when the ambient group is linearly
reductive. `linearlyReductiveReducedIdentity` uses that the open identity
component of a reduced scheme is reduced. Its reduction inclusion has an
actual inverse from the reduction lift of the identity, and multiplicative
type transports from the torus along this isomorphism.
