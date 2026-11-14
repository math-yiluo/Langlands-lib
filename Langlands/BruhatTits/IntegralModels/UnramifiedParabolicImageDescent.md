# Parabolic images of recovered neutral models

This derived unit connects compatible full and neutral unramified recovery to
the actual schematic image of a neutral special-fibre comparison. All
constructions and results are at arbitrary universe `u`.

Fix a nonarchimedean local field `F`, component model data `D₀`, `D₁` over
its integers, component model data `E₀`, `E₁` over the maximal-unramified
integers, and recoveries `e₀`, `e₁`. The comparisons
`φ : RelativeComponentModelHom D₀ D₁` and
`ψ : RelativeComponentModelHom E₀ E₁` are supplied.

`UnramifiedComponentModelRecovery.neutralSpecialFibreIso` takes the actual
residue base change of the neutral recovery isomorphism. Its base field is
the residue field of `fixedFieldIntegers F`.
`neutral_specialFibre_comparison_comm` applies this residue base-change functor
to `neutral_comparison_comm`. Thus the coefficient extension of `φ` and the
supplied `ψ` form an isomorphic square on the actual neutral special fibres.
No further compatibility hypothesis on these two maps is needed: the
imported integral comparison theorem derives their compatibility from
generic rigidity.

`specialFibreImageIso` applies the schematic-image comparison for an
isomorphic square. Its source is the schematic image of the special-fibre
map of the actual unramified coefficient extension of `φ.neutral`; its
target is `ψ.specialFibreImage`. The theorem
`specialFibreImageIso_hom_comp` records compatibility with the specified
inclusions into the ambient neutral special fibres.

Finally, `hasParabolicSpecialFibreImage` assumes that the actual image of
`ψ` is parabolic. It reverses the isomorphic square to transfer this
parabolicity to the image of the coefficient extension of `φ.neutral`.
`Hom.isParabolic_specialFibreImage_of_unramified` then reflects parabolicity
to the original residue field. The conclusion is exactly
`φ.HasParabolicSpecialFibreImage`.

The provenance is internal and derived: the proof composes the published
recovery comparison, schematic-image transport, and parabolicity reflection
interfaces. It does not assert model recovery or upstairs parabolicity
without their supplied hypotheses, and it makes no reduction-preimage
claim.
