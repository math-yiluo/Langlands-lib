# Fixedness of the identity coset and subgroup containment

This internal adapter works over any base scheme `S : Scheme.{u}`.
For an actual relative morphism `q : G.X ⟶ Q`,
`quotientIdentityPoint q` is the identity section of `G` followed by `q`.
`comp_quotientIdentityPoint` identifies its pullback to any test scheme
with that test scheme's identity group point followed by `q`.

Suppose a subgroup functor `H` and the morphism `q` satisfy the exact
right-coset fiber law on every scheme test:
`q(g) = q(h)` if and only if `g⁻¹ * h` belongs to `H`. Suppose an actual
`SchemeAction G Q` satisfies `a.act g (h ≫ q) = (g * h) ≫ q` on every
scheme test. For any group-scheme homomorphism `i : K ⟶ G`,
`SchemeAction.isFixed_quotientIdentityPoint_iff` proves that the identity
coset is an all-test fixed point under the action restricted along `i`
if and only if `SubgroupFunctor.range i ≤ H`.

In the forward direction, fixedness says that the image of every
`K`-point has the same quotient image as the identity. The fiber law
then puts that image in `H`. Conversely, containment and the fiber law
identify these quotient images on every test scheme, and the action
law gives fixedness after every refinement of the identity coset.

The construction and proof are internal consequences of the supplied
all-test fiber and action laws, for converting the flag-step fixed-point
conclusion into its required subgroup containment. No quotient existence,
flatness, field, smoothness or monicity hypothesis is needed for this
criterion. It supplies neither fixedness of the identity coset nor the
invariant affine neighbourhoods used to prove that fixedness.

`quotientIdentityPoint` abbreviates the existing
`HomogeneousQuotient.identityCoset G q`; its underlying section is unchanged.
