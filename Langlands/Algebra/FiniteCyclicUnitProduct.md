# Cyclic products in finite commutative rings

Let `σ` be an automorphism of a finite commutative ring `S` with `σ^l = 1`
and `l > 0`. Suppose the first `l` conjugates of some scalar have unit
pairwise differences. This module derives that every `σ`-fixed unit of `S`
is the product of the first `l` conjugates of a unit of `S`. This applies
to finite coefficient quotients of the integral order used in the unit
fundamental lemma.

For a unit `u` with cyclic product one, the operator applying `σ` and then
multiplying by `u` has period `l`. Its fixed elements span `S` by cyclic
semilinear interpolation. Choose a fixed element with nonzero image in as
many maximal-ideal quotients as possible. If it vanishes at a maximal ideal,
spanning gives another fixed element whose image there is nonzero. The set
of maximal ideals containing the first element is preserved by `σ`, since
`σ` changes this element by a unit factor. The Chinese remainder theorem
provides a coefficient that is one at precisely these ideals and zero at
the others. The product of its conjugates has the same residues and is fixed
by `σ`. Adding this coefficient times the second fixed element preserves
all nonzero residues and adds at least one. The maximal choice must therefore
be a unit, which expresses `u` as `x / σ(x)` for a unit `x`.

The cyclic product and the map `x ↦ x / σ(x)` are homomorphisms on the finite
commutative group `Sˣ`. The fixed-unit argument and telescoping identify the
kernel of the product with the range of the second map. Cyclic reindexing
puts the range of the product inside the kernel of the second map. The two
subgroups have the same cardinality by the kernel and image formulas, so
this inclusion is equality.
