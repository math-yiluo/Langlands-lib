# Base changes and the full-level locus

This internal construction proves the maximality property of the actual
full-level locus of a supplied ordered tuple `v : SectionTuple A g n`.
For positive `n` invertible on the original base `S`, and every actual
scheme map `b : S' ⟶ S`, the existing condition
`IsFull (pullbackTuple b v)` is equivalent to
`Set.range b ⊆ fullLevelLocusSet v`. There are no extra assumptions on the
new base, the morphism, the dimension of `A`, or a numerical torsion rank.

First, a basis of the pulled-back fibre transports back to a basis of the
original fibre through `levelBaseChangeLinear`. The published
`fibreTuple_pullback` identity identifies its entries with the original
tuple at the composite field-valued point. A basis with precisely these
entries gives unique actual kernel coordinates there, using the finite
linear-combination formula and `kernelLevelEquiv`.

For a point `x` of `S'`, suppose two original coefficient sections agree
at `b x`. Map the spectrum of an algebraic closure of the residue field
of `x` to `S'`. The image of its composite with the first section lies in
the second section's image. Open-immersion lifting and the section
equations therefore make their actual restrictions equal. Unique kernel
coordinates on the transported fibre basis identify the coefficients.
This proves the no-collision condition at `b x`.

For coverage, let `y` be any original torsion point over `b x`.
The scheme pullback point theorem supplies a point over the pair
`(y, x)` in the pullback of the torsion morphism along `b`. Map the
spectrum of an algebraic closure of that point's residue field into this
pullback. Its two projections give an actual kernel point over a
composite point of `S'`. The transported basis enumerates it.
Evaluating this equality of kernel morphisms proves that an original
coefficient section meets `y` over `b x`. The reverse implication of the
maximality equivalence is the image-contained base-change theorem in
`FullLevelLocus`.

`fullLevelLocusLift` factors any map carrying the full pulled-back tuple
through the actual open immersion of `fullLevelLocus`. Its factorization
equation holds as a scheme morphism, and the open immersion's
monomorphism property gives uniqueness. `fullLevelLocusHomEquiv` packages
the bijection between actual morphisms from any scheme `T` into this
locus and base maps `T ⟶ S` whose prescribed pulled-back tuple is full.
Its forward map is composition with the open immersion; its inverse is
the unique factorization just constructed.

The provenance is internal. The proof combines the existing ordered
tuple, actual torsion base-change, kernel and clopen-locus constructions
with Mathlib's scheme pullback point theorem and open-immersion lifting.
No generic torsion-rank formula, automorphism faithfulness or
representability theorem is used. This represents the condition on a
fixed supplied tuple over a fixed family; it supplies no ordinary moduli
space, no full-level existence assertion and no automorphism rigidity.
