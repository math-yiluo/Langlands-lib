# Separable invariance from the central additive-subgroup criterion

This internal reduction combines the actual separable-closure transport,
the central Galois norm obstruction, and faithfully flat reflection of
affine-line constancy.

`HasConstantAffineLineMaps.not_exists_central_additive_closed_subgroup_separable`
is unconditional: for every separable algebraic extension `K/k`, an affine
group scheme locally of finite type whose ground-field affine-line maps
are constant has no actual central closed one-dimensional vector subgroup
after scalar extension. A putative subgroup gives a standard central closed
additive line over `SeparableClosure k`. Closedness makes its underlying
relative morphism a monomorphism. The Galois obstruction
`not_isCentral_of_mono_galois`, applied to the possibly infinite Galois
extension `SeparableClosure k/k`, contradicts its centrality.

`WoundSeparableFromCriterionStatement` is the implication from the
published `UnipotentWoundCriterionStatement` to the unchanged published
`UnipotentWoundSeparableExtensionStatement`.
`woundSeparableFromCriterion` proves this implication. For a smooth connected
affine unipotent group, actual scalar extension preserves smoothness,
affineness, connectedness and the existing representation-based unipotence
predicate. The supplied criterion over `K`, together with the unconditional
absence result above, gives affine-line constancy over `K`.
`HasConstantAffineLineMaps.of_fieldExtension` gives the reverse implication
by faithfully flat reflection.

The criterion remains an explicit hypothesis of this reduction. This module
does not prove that hypothesis or claim an unconditional proof of the full
separable-extension proposition. Neither the original proposition nor its
all-morphism constancy predicate is changed. The extension may be infinite,
and no restriction is imposed on the characteristic, field cardinality or
perfectness.

The construction is internal: its provenance consists of the named
coordinate, base-change, Galois norm, reflection and geometric transport
results, rather than an external structural assertion used without proof.
