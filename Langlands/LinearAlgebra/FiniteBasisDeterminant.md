# Mixed finite-basis determinant units

This internal algebraic construction supplies determinant transition units when
two actual finite bases of the same module may have different finite index
sizes. The coefficient ring is any commutative ring, including the zero ring;
the module is an actual module over that ring.

`sameUnit` is the determinant of the coordinate matrix from the second basis
to the first, with the determinant of the reverse coordinate matrix as inverse.
`rank_eq` uses the invariant basis number theorem over a nontrivial commutative
ring. Its contrapositive, `subsingleton_of_rank_ne`, says that unequal ranks
force the coefficient ring to be trivial.

`unit` transports the first basis along equality of its size with the second
size and takes `sameUnit`; if the sizes differ, it returns `1`. In that branch
the coefficient ring and its unit group are subsingletons, so there is no
choice of transition unit. `unit_self` and `unit_mul` prove the identity and
composition laws. When sizes agree, composition is determinant
multiplicativity applied to the product of the two coordinate matrices.
Otherwise the subsingleton result proves the equality.

`map_unit` proves compatibility with a ring homomorphism when the coordinate
coefficients of the two supplied pairs of bases are carried to each other.
For equal sizes, it applies the ring map to the coordinate matrix determinant;
for unequal sizes, both defined units are `1`.

The construction is derived from Mathlib's actual bases, coordinate matrices,
determinants, and invariant basis number theorem. It is intended to support
determinant lines for locally free sheaves of variable finite rank. It makes
no claim about the existence of such local frames or parabolic representability.
