# Pointed affine-line capture and constant split kernels

Author: Worker 1371.

This internal construction concerns actual group schemes over an arbitrary
field. `CapturesPointedAffineLineMaps s` says that every relative-scheme
morphism from the affine line which sends zero to the identity factors through
the supplied group homomorphism `s`. The factoring morphism need not be a
group homomorphism. There are no smoothness, affineness, connectedness or
commutativity hypotheses.

`CapturesPointedAffineLineMaps.of_productIso` starts with an actual
group-scheme isomorphism `G ≅ V ⊗ W` and affine-line constancy of `W`.
The second product coordinate of a pointed map is the identity, so the map
factors through the first-factor inclusion, transported by the inverse
isomorphism. This proof uses the product point equivalence to compare both
coordinates. `mem_range_comp` transports capture along a monic subgroup
inclusion for pointed ambient maps which factor through that inclusion.

`HasConstantAffineLineMaps.pointed_eq_one` evaluates a constant map at zero to
show that a pointed map is the identity. The theorem
`CapturesPointedAffineLineMaps.of_constant_quotient` applies this observation
to a quotient homomorphism. Every pointed affine-line map lands in its full
scheme-theoretic kernel. A supplied inclusion of kernel range into the range
of `s`, on every relative scheme test, therefore proves capture by `s`.

`kernel_hasConstantAffineLineMaps` takes homomorphisms `q : G ⟶ H` and
`s : H ⟶ G` with `s ≫ q = id`, and capture by `s`. Normalize a map into
`kernel q` by dividing by its value at zero. Its image in `G` factors through
`s`. Applying `q` shows that the factoring map is the identity, so the
normalized kernel map is the identity by the monic kernel inclusion. This
proves constancy of the original map.

These are formal consequences of the existing affine-line normalization,
full scheme-theoretic kernel and subgroup-range constructions. They require
no new external mathematical input. Applied over a separable closure they
supply the constancy implication needed after a vector factor and its
retraction have been constructed in the proof of CGP, *Pseudo-reductive
Groups*, second edition (2015), Theorem B.2.5. They do not construct those
structural data.
