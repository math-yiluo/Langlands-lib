# Rigidity on the closure of a centralizer product

Implementation by Worker 1438, using Worker 1386's split-torus homomorphism
family rigidity. The module constructs the lift into a containing monic subgroup of
every inverse-conjugate point and proves multiplicativity and naturality. Composing
with a homomorphism to a split torus gives a family to which `HomFamily.eq_of_connected`
applies. At a parameter mapping to the identity the lifted conjugate is the original
restricted homomorphism.

The reduced closure of the centralizer product contains the identity section: its
image lies in the product image, and the vanishing-ideal factorization theorem for
reduced sources lifts that section into the actual closure. Connectedness and the
all-test inverse-conjugation condition are supplied by `CentralizerProductTransporter`.
The final theorem identifies the projected conjugation family with the fixed
projection of the cocharacter restricted to the containing subgroup.

The general `ConjugationInto` construction works over any base scheme. Its
`conjugatePoint` chooses a preimage using the all-test predicate `Holds`;
monicity of the containing morphism makes this choice unique. Postcomposing with
that morphism proves the multiplication and naturality identities by cancellation.
`projected_conjugatePoint_eq` assumes both the source and projection target are
split tori and the parameter scheme is connected. The identity-parameter version
also takes an actual source homomorphism into the containing subgroup.

The `CentralizerProduct` specialization works over any field. Its final theorem
`projected_conjugation_eq` assumes the morphism `j` represents the dynamic
centralizer of the cocharacter, its full subgroup-functor range lies in the closed
subgroup `b`, and both factors are smooth, affine and connected. The explicit
monicity instance for `b` is redundant with its closedness and allows the
restricted cocharacter to elaborate in the theorem's type. The projection
`q : B ⟶ D` is supplied, with `D` a split torus. All conclusions quantify over
every test scheme and every point and refinement used in the conjugation family.
No algebraic closure of the field is needed.

This is internal infrastructure derived from the published centralizer-restriction,
vanishing-ideal and group-scheme interfaces and the accompanying
`Torus.HomFamilyRigidity` implementation. The product-closure input is the
separately reviewed `CentralizerProductTransporter`. No assertion from the
literature is assumed. The module proves no existence theorem for a solvable
torus quotient, no closedness of the multiplication image and no Borel conclusion.
