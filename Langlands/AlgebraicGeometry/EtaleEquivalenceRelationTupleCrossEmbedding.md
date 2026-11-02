# Closed cross-correspondences between symmetric tuple schemes

This internal helper continues the symmetric-tuple construction motivated by
Stacks Lemma 68.8.3, Tag 0BBN, first proof paragraph. Its registered source is
`stacks-stratification-2026-11-02`, directory SHA-256
`844f29708bb7e14d69fe37b2251bb94ea49065647c1257aaaeb4655ac6a1288e`.
Actual affine quotients are constructed in the preceding helpers through the
published specialization of Stacks Proposition 39.23.9, Tag 03BM, registered as
`stacks-finite-flat-groupoid-quotient-2026-11-01`, directory SHA-256
`04098502d60fbca6624b86128e0360936b8a62bff64fa4765db553d0f7466304`,
`03BM.txt`, statement and proof. The present calculations are derived from
those constructions and scheme fibre-product universal properties; neither
source is claimed to state this exact API.

`isClosedImmersion_of_isPullback_of_affine_fpqc` proves descent of closed
immersions in a cartesian square of affine schemes when the change of target
is flat and surjective. Global sections turn the square into a ring pushout.
The target-change ring homomorphism is faithfully flat, and the base-changed
ring homomorphism is surjective because its scheme map is a closed immersion.
Faithfully flat descent of surjectivity proves surjectivity of the original
ring homomorphism, which gives the required closed immersion. This is a derived
affine descent calculation using Mathlib's ring theorem.

For an étale equivalence relation `E` with separated source map,
`tupleCross_isPullback_relation` identifies the joint ordered cross endpoint
with the base change of `prod.lift E.t E.s` along the product of the two zeroth
coordinate maps. Its proof uses the universal cross lift, and uniqueness follows
from extensionality in the two tuple endpoints. Consequently
`tupleCross_joint_isClosedImmersion` proves that this ordered joint endpoint is
a closed immersion whenever the original relation map is a closed immersion.

When `E.U` and `E.R` are affine, `tupleSymmetricCrossJoint` defines the morphism
from the symmetric cross scheme to the product of its two symmetric tuple
schemes by pairing the two endpoints. `tupleSymmetricCrossJoint_fst` and
`tupleSymmetricCrossJoint_snd` give its two projections.
`tupleSymmetricCross_isPullback` identifies the
joint ordered endpoint as the base change of the joint symmetric endpoint along
the product of the ordered-to-symmetric quotient maps. Independent permutations
make the ordered joint endpoint equivariant for the same product group on its
source and target. The product-action helper identifies the product of the two
symmetric quotients as an actual quotient of the product tuple scheme. The
equivariant quotient-map theorem gives the cartesian square. Its descended map
is the pair of the previously defined symmetric endpoints, as checked after
precomposing with the cross quotient map using the coequalizer uniqueness law.

`tupleSymmetricCross_joint_isClosedImmersion` applies the preceding affine
descent calculation. The product quotient map is flat and surjective, and its
base change is the ordered closed immersion. Thus the actual symmetric
cross-correspondence embeds as a closed subscheme of the product of its two
symmetric tuple schemes. `tupleSymmetricCrossJoint_isClosedImmersion` records
this property for the named joint morphism.
The universe `u` is arbitrary throughout. These
results do not yet prove étaleness of the descended endpoints, their relation
laws, the tuple stratification, or the Noetherian first-level statement.
