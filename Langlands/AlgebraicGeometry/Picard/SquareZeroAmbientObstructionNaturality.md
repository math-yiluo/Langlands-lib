# Actual Picard obstruction under a quotient of the ambient thickening

This is an internal derivation from the actual square-zero unit sequence,
its cohomological boundary, the actual Picard/H¹ comparison, and the
published composition and boundary identities for homeomorphic pushforward.
It treats schemes in an arbitrary common universe `u`.

## Actual maps for nested schemes

Let `b : Y → X` and `j : Z → Y`. The underlying module map
`kernelModuleMap b j` sends a section `a` of the actual structure-map
kernel for `j ≫ b` to `b.app(a)`, a section of the pushforward of the
actual kernel for `j`. The equation defining the original kernel is
exactly the equation needed in the target. Naturality follows from that
of `b.app`, and linearity follows from preservation of multiplication.
`kernelModuleMap_app` records this actual value. No immersion or
nilpotence hypothesis is required for this construction.

The underlying abelian-sheaf map is `sequenceKernelMap`. The middle map
`sequenceMiddleMap` is the published actual unit reduction along `b`.
The quotient map `sequenceQuotientMap` is the identity on the inner unit
sheaf after composing the two actual pushforwards.

Assume `j` and `j ≫ b` are closed immersions with square-zero ideals,
with proofs `hj` and `hjb`. The two squares commute: the first because
`b.app(1+a) = 1+b.app(a)`, and the second by the actual composition of
structure maps. `unitSequenceMap` bundles these three maps as a morphism
from the square-zero unit sequence for `j ≫ b` to the pushforward along
`b` of the sequence for `j`.

## Cohomology and obstruction naturality

Assume also that `b` is a closed immersion with nilpotent ideal, with
proof `hb`. Its topological map is a homeomorphism. In every degree `n`,
`idealCohomologyMap b j hb n` is the additive homomorphism from actual
ideal-module cohomology for `j ≫ b` to that for `j`. It first uses the
inverse actual ideal/abelian-sheaf comparison, then the cohomology map of
`sequenceKernelMap`, then homeomorphic pushforward, and finally the
actual ideal/abelian-sheaf comparison for `j`.

The private `quotientCohomologyComparison` identifies the iterated
pushforward comparison on inner unit cohomology with the comparison for
`j ≫ b`. It uses the published composition identity and the equality of
the actual nilpotent closed-immersion topological isomorphisms.
`boundaryMap_naturality` then proves in every degree

```text
boundaryMap j hj n y
  = idealCohomologyMap b j hb (n+1) (boundaryMap (j ≫ b) hjb n y).
```

The proof applies naturality of the connecting homomorphism to
`unitSequenceMap`, uses its identity quotient map, and then uses the
published compatibility of the connecting homomorphism with
homeomorphic pushforward. These results need no compactness hypothesis.

When `Z` is quasi-compact (`CompactSpace Z`), the actual Picard/H¹
comparison turns this equation in degree one into
`obstructionMap_naturality`. `obstructionMap_comp` gives the equality of
additive homomorphisms. Vanishing of the larger obstruction implies
vanishing of the smaller one; `obstructionMap_eq_zero_iff` reflects
vanishing when the ideal H² comparison is injective.

When `Y` is also quasi-compact, `picard_lift_iff_image_obstruction`
identifies liftability of an actual Picard class to `Y` with vanishing of
the image of its obstruction for `X`. The line-bundle version retains an
actual line bundle on `Y` and an actual module-sheaf isomorphism after
pullback. Both use the published square-zero lifting criterion and the
new obstruction identity. If `X` is also quasi-compact and the ideal H²
map is injective, `picard_lift_iff_of_injective` makes liftability to `X`
and to `Y` equivalent.

## Scope

All coefficient maps are induced by actual structure maps. No flatness,
coefficient-field section, residue-fibre tensor identification, or
vanishing of an obstruction group is assumed. Injectivity is an explicit
hypothesis only in the results which reflect vanishing or liftability.
Choosing equations that kill an obstruction, building a formal Picard
family or a hull, and constructing the smooth scheme atlas remain
separate obligations.
