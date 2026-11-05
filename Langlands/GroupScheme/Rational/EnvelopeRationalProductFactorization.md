# Rational product factorization from torus maps in the envelope

This internal construction uses the published invariance of the represented
fixed torus envelope under rational inner automorphisms and the published
same-source torus-map conjugacy theorem through a split unipotent kernel.
The stable-vector existence statement remains an explicit hypothesis;
linearization and affine torsor triviality use their published proofs.

For a supplied lift `sH : Q → H` into a torus-envelope representative `H`,
`rationalConjugateLift` composes it with the actual envelope isomorphism
induced by conjugation by a rational ambient point. Its composite into `G`
is exactly the original map followed by that inner automorphism. If the
rational point comes from the full kernel of `q : G → Q`, the quotient map
is unchanged.

Assume `Q` is a torus and the restriction `H → Q` is the represented fppf
quotient by a supplied smooth connected closed split unipotent kernel `V`.
The actual map `v : V → H` is required to be monic; closedness is unnecessary
for this conditional construction. Same-source torus-map conjugacy produces
a rational point of `V` that corrects the rational ambient conjugation.
`rationalTorusKernelCorrection` retains that point and its exact identity.

Suppose also that `V` maps into an ambient kernel `N`, compatibly with their
maps into `G`, and that a supplied subgroup `C → N` represents the inverse
image in `N` of the centralizer of `sH(Q)`. For a rational point `u` of `N`,
let `a` be the constructed correction in `V`. The two actual torus maps have
the same conjugation by `a` and `u`, so `a⁻¹u` centralizes the torus map on
every refinement. The representing equivalence lifts this remainder to a
rational point of `C`, and `u = a(a⁻¹u)` gives the rational product
factorization. This route does not require a separate equality between a
torus normalizer and its centralizer.

The factorization works over any field, with no finite-field hypothesis.
It depends on the supplied quotient, kernel and centralizer data; their
existence and geometry are separate obligations. The all-test centralizer
identity is proved from equality of actual homomorphisms, not inferred from
commutation of rational points alone.
