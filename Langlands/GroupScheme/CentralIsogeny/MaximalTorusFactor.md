# Factoring lifted homomorphisms through a compatible maximal torus

Let `p : G → H` be a central isogeny over an arbitrary field, with `G` connected
reductive. Let `i : T → G` be a maximal torus. Suppose a homomorphism
`t : T → T'` to a commutative group scheme and a homomorphism `i' : T' → H`
satisfy `i ≫ p = t ≫ i'`. Let `C` be any commutative group scheme and suppose
`a : C → G` and `b : C → T'` satisfy `a ≫ p = b ≫ i'`.

`IsCentralIsogeny.range_le_range_maximalTorus` proves that the range of `a` is
contained in the range of `i` as subgroup functors on every test scheme.
`maximalTorusFactor` constructs a homomorphism `C → T`, and
`maximalTorusFactor_comp` identifies its composite with `i` as `a`.
`maximalTorusFactor_unique` proves that this factor is unique.
If `i'` is a closed subgroup embedding, `maximalTorusFactor_comp_t` also
identifies the composite of this factor with `t` as `b`.

This is an internal consequence of the published all-test torus-centralizer
reflection and maximal-torus centralizer theorems. The two projected images
factor through the same commutative group scheme `T'`, so they commute after
every refinement of every test scheme. Reflection through `p` puts the image
of `a` in the centralizer of `i`. The published
`maximalTorusCentralizer` identifies this centralizer with the range of `i`.
The represented-subgroup `factorHom` construction then gives the actual
homomorphism. The closed embedding `i` gives uniqueness, and cancellation
along the closed embedding `i'` proves the second commuting identity.

No splitness of either torus, reducedness of test schemes, or characteristic
restriction is imposed. The result retains the compatible maximal torus and
the two commuting identities as hypotheses. It does not construct
quaternionic hyperbolic coordinates or identify a spin-kernel generator.
