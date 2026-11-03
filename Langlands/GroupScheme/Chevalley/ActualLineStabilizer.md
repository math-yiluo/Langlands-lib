# Line stabilizers for actual affine group schemes

`exists_line_stabilizer` proves the following for every field `k` in universe
`u`: if the structural map of an actual group scheme `G` is affine and
locally of finite type, and `i : H → G` is any closed subgroup, there are
`n`, a coordinate `j : Fin (n+1)`, and an actual matrix representation
`ρ : G → GL(Fin (n+1))` such that on every relative scheme `T`, membership
in exactly `SubgroupFunctor.range i` is equivalent to the equation
`ρ(x) e_j = a e_j` for some unit `a` in the ring of global sections of `T`.
The single representation and coordinate are chosen before quantifying
over test schemes.

The subgroup and ambient group need not be smooth, connected or reduced.
The field can be finite or imperfect and have any characteristic. The
quantifier includes nonaffine and nonreduced test schemes, and the
zero/full subgroup cases require no exceptions.

This internal transport completes the previously proved corepresented
line-stabilizer construction. First choose affine coordinate schemes for
`G` and `H`; the closed immersion into affine `G` makes `H` affine.
`affineMapNat` restricts the original homomorphism to affine tests, and
`modelMap` is its actual homomorphism between the corepresented affine
models. The global-section adjunction proves compatibility with the
original map on every test scheme. Full faithfulness of the group-valued
Yoneda embedding identifies the underlying maps of the existing model
isomorphism with precisely the chosen scheme isomorphism and its inverse.
Consequently the model homomorphism is conjugate to the original map by
these scheme isomorphisms, is closed, and has the corresponding actual
range on every test.

Local finite type of the structural morphism becomes finite type of its
affine coordinate algebra by the existing spectrum criterion. Apply
`exists_corepresented_line_stabilizer_fin`, then restrict the actual
representation along the inverse model isomorphism. The proved range
comparison and point-matrix restriction formula give the claimed
criterion for the original `G` and `H`.

The finite regular representation, subgroup-ideal subspace, adapted basis
and exterior line follow the route of Milne, *Algebraic Groups* (2017),
Theorem 4.27 and Lemma 4.28, printed pages 94–95; their proofs are in the
imported Chevalley modules. The present all-scheme transport is derived
from the actual relative spectrum adjunction and group-valued Yoneda
embedding, rather than an additional representability assumption. This
module supplies the line stabilizer for the homogeneous quotient task;
the projective map, scheme quotient and their geometric properties are
separate constructions.
