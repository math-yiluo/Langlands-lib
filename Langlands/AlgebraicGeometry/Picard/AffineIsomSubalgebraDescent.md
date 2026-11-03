# Specified Picard isomorphisms descend over affine bases

This internal unit proves exact section descent from affine finite-presentation
representability and applies it to the actual relative Picard Isom presheaf.
Its inputs are published Library constructions and scheme-morphism descent.
It introduces no new source theorem.

`HasAffineSubalgebraSectionDescent F` says that, for each commutative algebra
`A` over the fixed commutative ring `R`, each specified section `x` of `F` on
`Spec A`, and each finite set of elements of `A`, there is a finitely generated
`R`-subalgebra `B` containing that set and a section `y` on `Spec B` whose actual
restriction is exactly `x`. The equality retains the specified section.

The scheme-level helper applies the published finitely generated subalgebra
morphism-descent theorem with source the identity scheme over `Spec R`.
The pullback of that source to an algebra base is canonically the base itself.
The descended morphism is composed with this canonical section and the target
projection. The morphism-descent comparison, evaluated on the canonical
sections, gives equality of the original and restricted points in the slice.

A natural representation transports a specified presheaf section to a specified
scheme point. Descending that point and applying the natural representation
again gives the required section. Naturality and the inverse identity prove
exact equality with the original section. The helper needs only local finite
presentation of the representative; the public presheaf consequence uses the
existing affine finite-presentation representation predicate.

For a proper flat locally finitely presented scheme morphism and two actual
line-bundle families on any affine test base `Spec R`, the focused line-bundle
Isom representability proposition supplies the representation. The resulting
section is an actual isomorphism with the published coherent ordinary-pullback
restriction, since that is exactly what the relative Isom presheaf stores.
The existing Hom-to-Isom theorem gives the same conclusion from focused Hom
representability. These two applications retain that representability premise;
this unit does not assert its unconditional proof.

All rings, schemes and algebra tests retain the arbitrary universe `u`. There
is no field, noetherian, reducedness or flatness condition on the test algebra.
This is descent of a chosen arrow. It does not prove a filtered-colimit
category equivalence, infinitesimal gluing or a smooth chart.
