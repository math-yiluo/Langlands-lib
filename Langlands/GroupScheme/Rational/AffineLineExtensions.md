# Affine-line constancy under subgroups and extensions

Author: Worker 1478.

This internal construction develops closure properties of the existing
`HasConstantAffineLineMaps` predicate. It concerns actual group schemes
over every field `k : Type u`. No smoothness, connectedness, affineness,
unipotence or characteristic hypothesis is needed. Its provenance is
elementary group-object algebra together with the published actual
scheme-theoretic kernel and its all-test point equivalence.

`affineLineDifference a` is the actual relative scheme morphism
`a / (toUnit A ≫ (zeroSection ≫ a))`, where `A` is the affine line over
`Spec k`. It is the pointwise right quotient of the map by its constant
value at zero. The first lemmas show that this map takes the identity
value at zero, commutes with postcomposition by actual group
homomorphisms, and takes the identity value everywhere precisely when
`a` equals its constant value at zero.

`HasConstantAffineLineMaps.eq_to_zeroSection` gives the canonical
constant value for every affine-line map into a target satisfying the
predicate: precomposing its existential constant factorization with
the zero section identifies the value. Hence its normalized map is
the constant identity value.

`of_mono` proves that constancy passes to a group whose underlying
scheme has any monic relative scheme map into the constant target.
The map need not preserve the group structure. Apply constancy to
the composite, choose the zero-section value in the source group,
and cancel the monomorphism. `of_closed_subgroup` applies this to
actual closed subgroup inclusions.

`of_kernel_range_le` proves the extension principle. Given an actual
homomorphism `q : G ⟶ Q`, assume that `Q` has constant affine-line maps
and that the full kernel range is contained in the range of a supplied
homomorphism `j : H ⟶ G`, with `H` also having constant affine-line
maps. Normalize any map into `G` at zero. Its composite into `Q` takes the
identity value, so the existing `mem_range_kernelι_iff` identifies it as a
point of the full kernel range on the test scheme `A`. The range
containment supplies an actual lift `b : A ⟶ H.X`. Constancy of `b`
makes its image constant; its value at zero is the identity by
normalization, so the normalized map takes the identity value everywhere. Therefore the
original map is constant at its zero-section value.

`of_kernel` specializes to `H = kernel q` and `j = kernelι q`.
This proves stability under actual group-scheme extensions without
any surjectivity hypothesis on `q`. All kernel-range containments use
the existing functors on every relative test scheme. No assumption
of rational-point-only lifting or fppf-local lifting is substituted
for the supplied range containment.

The range-containment formulation is conditional and does not prove
constancy of a quotient of a constant group. These lemmas do not
construct central additive subgroups, anisotropic presentations, the
wound quotient of a split radical, or the host pseudo-parabolic
rational-lifting theorem.
