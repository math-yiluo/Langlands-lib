# Root valuations of torus points in the abstract center

This is an internal construction and deduction from the published actual
normalizer action and root-system realization. It introduces no new external
literature assertion.

`torusPointCharacterValue` evaluates the actual character lattice at a rational
torus point as an additive homomorphism into the additive form of the field's
unit group. For a monomorphic torus map, if the image of that point belongs
to the full abstract center of the rational-point group, every normalizer's
inverse torus automorphism fixes it. The proof evaluates the actual inverse
conjugation identity, uses abstract centrality, and cancels the monomorphism.
It follows that character evaluation is invariant under the actual normalizer
action on characters, whose convention is inverse pullback.

For an affine ambient group over an arbitrary field, splitness of the torus
and `HasRelativeRootSystem i` give a reflection for each actual relative
root in the actual normalizer/full-centralizer quotient. Choosing a rational
normalizer representative and using the reflection's action on the root
shows that its value at the point equals its inverse. The value therefore
has square one. With any `ValuativeRel k`, multiplicativity of the valuation
and order imply that this root value has valuation one. No comparison between
the abstract center and the rational points of the scheme center is used.
The field has arbitrary universe `u`; positive rank, local-field topology,
reductivity and genericity are not needed for these deductions.

`not_isNoncentralNegativeTorusPoint_of_mem_center` applies this valuation
identity to every actual simple root. The strict inequality required by the
noncentral-negative test contradicts valuation one, including when the
simple-root type is empty.

`not_isNoncentralNegativeTorusPoint_of_fullIndex_center` specializes to the
actual full-index standard Levi. It retains the global
`StandardCocharacterStatement`, connected reductivity of the ambient group,
maximal splitness, genericity of the selected cocharacter, the actual
root-system predicate, and a finite simple-root type. The published
`levi_univ_eq_top` makes this Levi the entire rational-point group, so a point
of its abstract center gives exactly the ambient centrality needed above.
This discharges the full-index exclusion used by the factor exponent lemmas;
it supplies neither proper-index Jacquet vanishing nor scalar-character
bounds, analytic sufficiency or the exact self-association target.
