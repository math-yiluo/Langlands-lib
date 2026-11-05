# Parameter families of affine-line maps into a wound target

This internal construction adapts the published affine-line constancy
predicate to actual parameter families. It is derived from
`HasConstantAffineLineMaps.eq_to_zeroSection`, the Cartesian product
identities, and the dense-rational-point equalizer lemma in
`RationalDensityExt`. It is not a literal extraction from a source theorem.

Over any field `k`, let `P` be a relative scheme and let `W` be an actual
group scheme with `HasConstantAffineLineMaps`. The morphism
`affineLineParameterZeroSection P` sets the affine-line coordinate to zero
and retains every parameter. The morphism `affineLineParameterSlice p`
inserts an actual rational parameter `p`. Their compatibility with the
ordinary zero section is proved as an equality of relative scheme
morphisms. Every rational point of the product factors through its
rational-parameter slice.

`family_eq_parameter_restriction` assumes that the actual product
`AffineLine.scheme (Spec k) ⊗ P` is reduced and has dense rational points,
and that `W` is separated over `k`. It proves that every relative scheme
morphism from that product to `W` factors through the parameter projection,
with value given by restriction along the whole zero section. The proof
specializes at each rational parameter, uses affine-line constancy, then
applies `hom_ext_of_denseRationalPoints` to recover equality of the actual
scheme morphisms.

`family_eq_one_of_zeroSection` consequently proves that a family whose
whole zero section is the group identity is identically the group
identity. The parameter scheme is not replaced by its rational points in
either conclusion.

These lemmas retain density and reducedness as explicit hypotheses.
They establish no density result over separably closed fields and no
descent assertion. They supply neither the vector-factor decomposition nor
the final all-field central-additive-subgroup criterion.
