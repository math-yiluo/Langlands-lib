# Monic homomorphisms from smooth connected affine groups

`Langlands.GroupScheme.HomImage.isClosedSubgroup_of_mono` proves that a
homomorphism from a smooth connected affine group over any field to an affine
group locally of finite type is a closed immersion when its underlying
morphism over the field is monic. The field and all schemes lie in an
arbitrary universe.

This is an internal deduction from the published `HomImage.exists_image`.
That factorization is a flat, surjective, quasi-compact homomorphism followed
by a closed immersion. Monicity of the composite makes its first factor
monic. Mathlib's `Flat.isIso_of_surjective_of_mono` makes that factor an
isomorphism, so its composite with the closed immersion is closed. No
centre-containment or quotient-existence premise enters this argument.
