# Orthogonal frames of Cayley algebras

`leftFrameBasis` constructs an orthogonal basis of a Cayley datum over a field of characteristic different from two. The input consists of orthogonal trace-zero vectors `x,y` of nonzero norm and a vector `z` of nonzero norm orthogonal to `1,x,y,xy`. The basis consists of `1,x,y,xy,z,xz,yz,x(yz)`, indexed by two copies of `Fin 4`. The norms in the second block are the norms in the first multiplied by the norm of `z`.

The polarized composition identities give skew-adjointness and the square of left multiplication by a trace-zero vector. Left multiplications by orthogonal trace-zero vectors anticommute. These identities provide the two generator matrices on each block and the sign for commuting an orthogonal left multiplication past a block word. The norm pairing makes each block orthogonal. The span of the first block is stable under both generators, so skew-adjointness puts the second block in its orthogonal complement. All eight vectors have nonzero norms and are linearly independent. The dimension of the datum gives the basis.

This is a derived form of the orthogonal doubling construction in Knus, Merkurjev, Rost and Tignol, *The Book of Involutions*, §33.C, Lemma 33.16 and Theorem 33.19, pp. 458–461.
