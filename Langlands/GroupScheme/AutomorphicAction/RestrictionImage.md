# Automorphic actions on the image of restriction of points

This is an internal formal consequence of the published
[`AutomorphicAction`](../AutomorphicAction.md) interface. It adds no structural
theorem about reductive groups or local fields.

For any two tests `U`, `T` over a scheme `S`, a test morphism `res : T ⟶ U`
and an automorphic action `a` of `H` on `G`,
`a.PreservesRestrictionImage res x` says that the automorphism induced by
`x ∈ H(T)` maps the image of `G(U) → G(T)` onto itself. Both images are
expressed by existential witnesses, so injectivity of restriction is unnecessary.

Naturality shows that a point restricted from `H(U)` preserves this image;
acting by its inverse gives surjectivity. The preservation property is closed
under multiplication and inversion, using the action laws.

Suppose `p : G ⟶ H` is a group-scheme homomorphism and its image acts on
`G(T)` by conjugation, as expressed by the explicit premise `hlift`.
`conjugacy_iff_exists_preservesRestrictionImage` proves that
`a(x)(G(U))` is conjugate to the restriction image by a point `h ∈ G(T)`
if and only if `p(h)⁻¹ x` preserves that image, for some `h`.
The proof applies the inverse action to the asserted equality of images,
and reverses this operation for the converse.

`conjugacy_iff_factorization_of_preservesRestrictionImage` then derives the
factorization criterion `x = p(h) res(y)` from the additional premise that
every acting point preserving the image is itself restricted from `H(U)`.
This premise is retained. In the hyperspecial conjugacy application, it is
the substantive integral-normalizer assertion; this module does not prove it.
