# Semidirect reduction with actual ambient weight support

This internal module treats an actual action of a smooth connected affine
group `K` on a smooth connected affine group `G` over any field and at arbitrary
universe `u`. A commuting split-torus action on `G` is lifted to the actual
semidirect product, fixing its acting coordinate.

`zeroCharacterSemigroup` has precisely the zero character as its carrier.
Its literal semigroup sum with any semigroup `A` is `A`; this includes an
empty semigroup and inserts no zero into `A`.

`semigroupSubgroup_isStable_inner` assumes the existing global
`SemigroupIntersectionStatement`. Every acting point belongs to the
zero-character semigroup of the lifted action. The closed normal inclusion
carries an `A`-semigroup point into the ambient `A`-semigroup. The published
all-test `semigroupCommutator` theorem puts their commutator in the literal sum
of those semigroups, hence in `A`. Multiplication by the normal point gives its
conjugate. The stated intersection comparison identifies the inverse image
along the normal inclusion with the exact original semigroup subgroup.
Thus inner stability holds for every `A`, whether or not it contains zero.

The two support-containment lemmas use the actual equivariant monomorphic
inclusions. They place the normal-factor support and the support of the
trivially acted-on acting factor in the actual ambient support, retaining
occurring zero characters.

These are derived constructions and proofs using the imported actual
subgroup functors, actions, lattice, and all-test commutator theorem. The
original API keeps its global intersection premise explicit. The local API
keeps only the inverse-image equalities described below. This module does
not establish the full solvable ordered-product statement.

`semigroupSubgroup_isStable_inner_of_comap` uses only the exact inverse-image
equalities along the normal inclusion for this lifted action. Its commutator
argument is unchanged. The original `semigroupSubgroup_isStable_inner` theorem
retains its full-intersection signature and supplies these local equalities.
