# Coroot-trivial torus maps and rank-one cell relations

This internal construction uses the actual ring cell calculus
`RingRootCell.WeylData` and the injective generic-line specialization from
`LocalSplitGeneratorRelations`. It imposes no field, reducedness,
noetherian, locality or characteristic assumption on the coefficient ring.

For supplied `CellData D` over a commutative ring `R` and a group-scheme
homomorphism `q` from its commutative torus `D.T` to `Q`,
`D.torusCellProjection q` is the actual morphism from the rank-one
coordinate cell to `Q` that projects to its torus coordinate and then
applies `q`. `lift_torusCellProjection` records that its value at coordinates
`(y,t,x)` is exactly `q(t)`.

For the invariance results, the additional supplied `WeylData` include the
actual cocharacter `h`, its root pairing two, the reflection normalizer,
the square-in-torus identity, and the global unit cell coordinates required
by the published ring calculus. The explicit hypothesis `hq` says that
`q(h(c)) = 1` for every relative scheme test and every unit `c` on that
test. Both the ambient group `D.G` and the target `Q` are assumed affine.
No existence of Weyl data is claimed here.

`torus_quotient_eq_of_cellPt_relation` proves, on every relative scheme
test, that
`cellPt(y,t,x) * B(z) = cellPt(y',t',x')`
implies `q(t) = q(t')`, with no condition on the scalar `z` or on a
Bruhat denominator. Here `B` is the actual negative-root point and
`cellPt(y,t,x) = B(y) * (i(t) * A(x))`. In particular, this is a statement
about full scheme-valued points, including nonreduced tests.

The implemented proof first assumes the denominator `d = 1 + x*w` is
a unit and writes `z = beta*w`, with `beta` the pulled-back global beta
coordinate of the Weyl data. The published all-test rank-one relation
computes the translated cell point with torus coordinate `t*h(d)`.
Torus equivariance and additive root multiplication give
`cellPt_mul_B_of_unit`. Injectivity of the open cell then identifies the
torus coordinate in any other cell factorization, and `hq` removes `h(d)`.

For an arbitrary relation over a local test ring `B`, the proof deforms
`w` to `w+X`. At `X=0` the product has the given cell factorization.
Openness of the cell therefore factors the deformation over the local
ring of the line at its closed point `X=0`. In the local ring at the
generic point of the closed fibre, the denominator
`1 + x*(w+X)` is a unit: its evaluation at `X=-w` is one, so it cannot
vanish identically on that fibre. The unit-case formula now applies.
The map from the first local ring to this generic local ring is
injective, by the published non-zero-divisor argument for polynomials
with a unit coefficient. Since `Q` is affine, the equality of torus
quotient values descends along this injection. Specialization to `X=0`
and injectivity of the cell recover the originally specified torus
coordinate `t'`.

Finally, morphisms to an affine scheme are detected by all local-ring
points, preserving the entire scheme structure. Applying the local-test
result after each such restriction proves the assertion for every
relative scheme test. No reduced-fibre equality or pointwise field
detection is used.

This unit retains supplied Weyl data and coroot annihilation. Applying
it to actual reductive-group rank-one centralizers, constructing the
ambient quotient, and proving the full relative derived-group
existence statement remain separate steps.
