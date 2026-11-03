# Field extension of actual Lie-kernel witnesses

This module is internal, derived infrastructure for the arbitrary-field form of
the rank-one solvable obstruction. It introduces no new assertion from the
literature. It uses the published actual scheme-pullback comparison in
`Lie.BaseChange`, the tensor scalar-extension equivalence and weight-vector
transport in `Torus.WeightBaseChange`.

`Lie.kernelFieldExtension` sends a dual-number point in the identity kernel over
the original coefficient ring to its coefficient extension, then uses the
inverse scheme-pullback comparison to obtain a tangent point of the base-changed
group. This construction and its compatibility with group homomorphisms work
over commutative rings, without affineness assumptions.

For an affine group locally of finite type over a field, the construction agrees
with the published linear scalar-extension equivalence on the pure tensor
`1 ⊗ x`. Tensoring a vector space with a field extension preserves the injectivity
of this pure-tensor map: the proof uses
`Module.Flat.tensorProduct_mk_injective`. Consequently distinct actual tangent
points remain distinct, and nonzero Lie vectors remain nonzero.

`weightSpace_lieImage_baseChange` transports exactly the witness expression used
in `RankOneSolvableObstructionStatement`: a nonzero weight vector together with a
dual-number identity-kernel point of the subgroup whose postcomposition is that
vector. Naturality of `Lie.kernelFieldExtension` transports the equality.
Affineness and local finite type are required for the ambient group only; the
subgroup in this lemma is arbitrary. All field-extension results allow every
characteristic and imperfect fields, with both fields in universe `u`.

These are transport lemmas. They do not prove exclusion of simultaneous
opposite-root witnesses, nor any geometric rank-one classification.

Local instances have explicit names prefixed by `fieldExtension` to
avoid generated-name collisions in combined imports. Their types and defining
expressions are unchanged.
