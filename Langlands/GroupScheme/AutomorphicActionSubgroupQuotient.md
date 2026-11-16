# Subgroup stabilizers under quotient actions

Worker 692. This is an internal derivation from the Library's all-test subgroup
stabilizers, fppf-local subgroup membership, and relative parabolic self-normalization.

Restriction of an automorphic action along a group homomorphism pulls back its
subgroup stabilizer. In particular, if the restriction is conjugation, the inverse
image of the action stabilizer is the all-test normalizer of the subgroup.

The module proves two descent facts. Inverse image along an fppf surjective group
homomorphism reflects containment in a subgroup functor with fppf-local membership.
Also, the stabilizer of a subgroup with fppf-local membership itself has fppf-local
membership. For the latter result, each further test map is pulled back along the
cover; naturality of the action gives the preservation equivalence there, and
membership in the original subgroup descends in both directions.

Consequently, if a subgroup is fppf-local and self-normalizing, any monic target
subgroup with that inverse image is exactly its stabilizer for an action restricting
to conjugation. This follows by reflecting the two inclusions along the quotient.

For a relative Borel in a reductive group over a ring, relative parabolic closedness
and the field-point Borel theorem discharge the published relative parabolic
self-normalizer theorem. Its all-test normalizer is therefore itself. A supplied
monic target subgroup with the original Borel as inverse image then represents its
action stabilizer. All fppf hypotheses and the inverse-image equality are explicit
inputs.

The construction `IsRelativeBorelSubgroup.quotientStabilizerInclusion` takes a
supplied quotient homomorphism from the Borel to a group `P`. This homomorphism is
flat, surjective and quasi-compact. Its kernel subgroup functor must equal the
inverse image, under the Borel inclusion, of the ambient quotient's kernel. The
ambient kernel must also lie in the original Borel. The ambient quotient is
flat, surjective and locally of finite presentation, and its action on the
original group restricts to conjugation.

The Library's `quotientSubgroupHom` constructs the induced map from `P` to the
ambient quotient. Exactness of the kernel gives its monicity, and kernel
containment gives its exact inverse image. The preceding stabilizer theorem
therefore certifies it as a representative of the original Borel's action
stabilizer. The result packages this actual map with its representation proof.
The module also retains the commuting quotient square.

This module does not construct either quotient group or its quotient projection,
prove a unipotent filtration or cocycle vanishing, or prove the semilocal
inner-form theorem. In particular, its construction does not establish the
existence or the structure of the quotient of a Borel by the center.
