# The matrix of the middle exterior pairing

For a commutative ring `A`, `middleExteriorPairing m A` pairs two elements of
`⋀[A]^m (Fin (2 * m) → A)` by taking the coefficient of the standard volume
element in their product. `middleExteriorGram m A` is its matrix `J` in
`matrixExteriorBasis (2 * m) m A`, whose indices are the `m`-element subsets
of `Fin (2 * m)`.

A row for a subset `S` has one nonzero coefficient, at the complement of `S`,
when `A` is nontrivial. This coefficient is the sign of the permutation that
orders `S` followed by its complement into the full ordered index set. The
entry formula holds over any commutative ring. Since complementation permutes
the exterior basis and each sign squares to one, the proof gives `Jᵀ J = 1`.
Thus `middleExteriorGramUnit m A` is the corresponding general linear group
element with inverse `Jᵀ`.

Interchanging two degree-`m` wedges contributes `(-1)^(m*m) = (-1)^m`. The
theorems `middleExteriorGram_transpose` and `middleExteriorGram_mul_self`
give `Jᵀ = (-1)^m J` and `J J = (-1)^m I`. The entry formula uses only the
images of integer signs and zero, giving `middleExteriorGram_map` for any
ring homomorphism out of `A`.

For `g : GL (Fin (2 * m)) A`, let `X` be its matrix under `exteriorGL` in
degree `m`. The full exterior action is multiplication by `det g`, since
its matrix has one entry given by the full minor. Multiplicativity of the
exterior algebra map and the volume coefficient then give
`Xᵀ J X = (det g) J` in `middleExteriorGram_similitude`.

The field version of the pairing and the signed complement basis computation
are in Knus, Merkurjev, Rost and Tignol, *The Book of Involutions* (1998),
(10.6), printed p. 117 (PDF p. 140). The product of the two complement signs
appears in (10.25), printed p. 126 (PDF p. 149). The entry computation and the
full-minor argument give the commutative-ring identities used here.
