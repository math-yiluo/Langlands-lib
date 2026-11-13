# Actual coefficient twists of integral models

This internal construction uses actual pullbacks of the published integral
models. It has no external existence claim. Its ingredients are the commuting
square comparison, stability of geometric properties under base change, and
generic rigidity of compatible model homomorphisms.

For a domain `R` with specified fraction field `K`, an integral model `N` of
`G`, and endomorphisms `a` of `Spec R` and `v` of `Spec K` satisfying
`v ≫ Spec.algebraMap R K = Spec.algebraMap R K ≫ a`, `N.twist a v hvc`
has actual group `a*N.group` and prescribed generic group `v*G`. Its generic
identification is the inverse square comparison followed by `v*N.genericIso`.
The affine, flat and locally finite-type properties are preserved by base
change. Smoothness is also preserved by base change.

`Hom.twist_generic_comm` rewrites a supplied compatible homomorphism from
this twist as the generic semilinear law: the pullback of `N.genericIso`
followed by the prescribed generic map equals the square comparison followed
by the generic pullback of the integral map and the target identification.
Its proof composes the compatibility equation with the square comparison and
cancels its inverse.

`twistIso` applies the published `Iso.ofHoms` to supplied extensions of a
generic isomorphism in both directions. Generic rigidity proves that the two
integral maps are inverse. `twistIso_generic_comm` records the same exact
generic semilinear law for the resulting actual isomorphism.

The general helper `baseChangeSectionHom_surjective` says that every section
of a group pulled back along a base isomorphism is the pullback of an original
section. Its proof projects the given section, precomposes with the inverse
base map, and verifies recovery using the pullback point correspondence.

These constructions do not extend any new generic map. In particular,
extensions from stable integral points and coherence of the resulting descent
datum still have to be proved to obtain KP Fact 2.10.16.
