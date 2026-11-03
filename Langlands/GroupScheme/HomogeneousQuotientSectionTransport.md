# Transport and composition of actual quotient sections

Author: Worker 1478.

This internal construction works over `Spec R` for every commutative ring
`R : Type u`, with no field or finiteness assumption. All schemes and maps are
actual objects and morphisms of `Over (Spec R)`. A section on an open `U` is
an actual map from `openOver R Q U`, whose composite with the projection is
the original open inclusion `openOverι R Q U`.

Given `q : X ⟶ Q`, `q' : X ⟶ Q'`, and a relative isomorphism `e : Q ≅ Q'`
with `q ≫ e.hom = q'`, `sectionAlongIso` transports a section on `U` to
`e.inv.left ⁻¹ᵁ U`. It first restricts the inverse comparison to that open
and then composes with the given section. `sectionAlongIso_comp` verifies
the section equation using the restriction square, the original section
equation, and the inverse identities. `localSections_of_iso` applies this
to the inverse image of each topological point.
`localSections_iff_of_iso` also applies the construction to `e.symm`.
Thus both directions concern every topological point of the supplied
models, without replacing these points by rational or geometric points.
The compatible comparison isomorphism is an explicit input.

`exists_affine_section` restricts a given section to an affine open
neighborhood `V` of any selected point in `U`. It uses the affine basis of
the underlying scheme and the existing relative inclusion
`openOverHomOfLE R Q hVU`. The conclusion includes both `IsAffine V` and
`V ≤ U`, along with the section equation for the same projection `q`.

For composable maps `f : X ⟶ Y` and `q : Y ⟶ Q`, suppose `f` lifts every
actual map `a : T ⟶ Y` from every affine relative scheme `T`. The
conclusion of that assumption is an actual `b : T ⟶ X` with `b ≫ f = a`.
`exists_section_comp_of_affine_lifts` first refines a section of `q` to
an affine neighborhood, then applies this hypothesis to that restricted
section. Associativity proves the resulting map is a section of `f ≫ q`.
`localSections_comp_of_affine_lifts` does this at every topological point.
In the other direction, `localSections_of_comp` simply composes each
section with `f`, so it needs no affine-lifting assumption.

The provenance is internal: the affine-open basis for schemes, restriction
of actual relative morphisms to target opens, inclusions between nested
opens, and category laws. This unit supplies the local-section composition
step for a possible split-radical reduction. It does not construct a
split-radical quotient, prove that a split-unipotent torsor lifts affine
tests, produce a quotient comparison isomorphism, or establish any
unconditional pseudo-parabolic local-section or rational-lifting theorem.
