# Lifting point characters over separably closed fields

This internal helper generalizes the lifting argument of the published
`Cartier.AlgClosedCharacterSeparation` module to separably closed fields.
Its proofs follow that module's interpolation and pointwise extensionality
route, using the separably closed section-extensionality theorem from
`FiniteEtale.PointwiseClosedImmersion`. No algebraic closedness is assumed.

`gm_hom_ext_of_isSepClosed` uses the representing equivalence between maps to
the multiplicative group and invertible global functions. Equality on rational
points gives equality of global functions, since the source is étale over a
separably closed field.

`exists_unit_pointValue_of_isSepClosed` interpolates prescribed nonzero values
and their inverses separately. Their products have value one everywhere, so
section extensionality shows that the resulting global functions are inverse.

`exists_gm_hom_of_points_of_isSepClosed` applies this construction to an
abstract homomorphism `G(K) → Kˣ` for a finite étale commutative group scheme
`G`. The representing equivalence produces a scheme morphism to the
multiplicative group. On `G × G`, both sides of its multiplication identity
agree on rational points because the abstract map is a homomorphism.
The product is étale, so the preceding extensionality proves the identity as
an equality of actual morphisms on all test schemes.

These lemmas supply the character-lifting step in the converse direction of
the corrected Milne, *Algebraic Groups* (2017), Example 12.28 statement.
They are derived helpers, rather than separate claims of a source theorem.
