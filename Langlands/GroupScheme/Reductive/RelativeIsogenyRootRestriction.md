# Actual root restrictions from a supplied root-datum isogeny

This internal derived module constructs the restriction of a compatible actual
homomorphism to supplied additive root parametrizations over a local ring. The
root-datum isogeny and actual character compatibility are hypotheses.

The source and target have supplied coordinate split tori and fibrewise full
reduced root data `P` and `Q`. A supplied isogeny `r : RootDatumIsogeny p Q P`
maps target weights to source weights and source cocharacters to target
cocharacters. Its transpose equation becomes the integer dot-product identity
`dot_coweightMap`, since the fibrewise data identify both pairings with the
coordinate dot product. A source cocharacter isolating a single root pair
therefore gives a target cocharacter isolating the corresponding root pair.
Reducedness and injectivity of the weight map justify the latter assertion.

For an actual torus homomorphism `tau`, compatibility with every actual
fixed-exponent character forces the corresponding actual cocharacter equation.
The proof compares coordinate projections and uses the transpose dot-product
identity. It is an equality of morphisms over `Spec R`, including when `R`
has nilpotents.

Suppose an ambient homomorphism `phi : G ⟶ H` has the given torus square, and
the target is reductive with the supplied fibrewise maximal torus. Then
`subgroup_le_comap` carries the source root of `r.indexEquiv b` into the target
root of `b` on every test scheme. The proof chooses an isolating source
cocharacter and its root coroot, transports both through `r.coweightMap`, and
constructs the required target field-fibre parametrizations from the actual
rank-one dynamic construction. Functoriality of dynamic centralizers and
positive subgroups transports each source point into the target dynamic
intersection. `LocalRootGroupDynamicCut` identifies this intersection with the
actual target root functor.

`rootRestriction` uses the represented-subgroup restriction construction on
supplied actual source and target root parametrizations. It is an actual
homomorphism `Ga R ⟶ Ga R`, and `rootRestriction_comp` states that its composite
with the target parametrization equals the source parametrization followed by
`phi`. The construction requires neither finiteness nor flatness of `phi`.
The unit-coefficient power formula and the full isogeny-rigidity theorem are
separate obligations.
