# Normalizer conjugation of the actual relative root subgroup functors

This internal supporting construction proves transport of the existing
`RelativeRoot.subgroup i a` directly from its orbit-extension definition. It is
valid over an arbitrary base scheme. The acting group is a commutative group
scheme, and the torus map needs only a monomorphism for its chosen Weyl action
to be defined. Smoothness, reductivity, root membership, splitness, and
representability of the root subgroup functor are not assumed.

A group homomorphism carries a full torus orbit and its extension through the
character `a` to the corresponding image orbit and extension. It preserves the
identity value at zero. Reparametrizing both the acting group map and the
character by a homomorphism also preserves the extension equation.

For a normalizing base point `n`, let `σ` be its automorphism of the acting
commutative group scheme. The defining identity is `i Int(n) = σ i`.
First compose an extension with `Int(n)` and then reparametrize the acting
group by `σ⁻¹`. The resulting acting map is again `i`, and the character is
`σ⁻¹ a`, which is precisely `weylAction i n a`. Thus conjugation by the
constant restriction of `n` carries every point of `U_a` into `U_{n a}`.
Applying the same inclusion to `n⁻¹` gives the reverse implication.

`subgroup_comap_innerIso` expresses this as an equality of the actual subgroup
functors on all test schemes. Its preimage orientation is
`Int(n)⁻¹(U_{n a}) = U_a`.
`normalizerConjEquiv i a n U` is the induced group equivalence of their points
over any test scheme `U`; its map is literal conjugation by the constant point
of `n`, and its inverse is conjugation by its inverse.

The provenance is internal: these results are formal consequences of the
published orbit-extension construction and the morphism-defined normalizer.
They do not assert the existence of rank-one normalizing representatives,
root subgroup realizations, or any of the geometric Tits axioms.
