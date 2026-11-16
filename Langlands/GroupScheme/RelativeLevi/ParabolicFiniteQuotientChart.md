# Finite smooth proper affine-base parabolic quotient charts

This internal construction assembles the published affine-base parabolic
quotients and their actual parabolic families on a finite scheme coproduct.
The hypotheses are a commutative ring `R`, a reductive group scheme `G` over
`Spec R`, a finite type `I` in the scheme universe, and relative parabolic
inclusions `j a : P a ⟶ G` for all `a : I`. The empty indexing type is allowed.

`affineParabolicQuotientComponents` chooses the published proper homogeneous
quotient for each inclusion. `finiteAffineParabolicQuotient` is the actual scheme
coproduct of these quotients over `Spec R`, bundled with proofs that its structure
morphism is smooth and proper. It uses `smoothProperCoproduct`, the component
smoothness theorem, and the properness carried by each chosen quotient.

`affineParabolicQuotientFamilies` uses the actual descended conjugate parabolic
on each quotient. `finiteAffineParabolicFamily` glues these families on the
coproduct. `finiteAffineParabolicChart` is the natural transformation from the
scheme's Yoneda presheaf to the actual parabolic presheaf induced by that family.
`finiteAffineParabolicChart_app_comp` identifies its value on a parameter lifted
to `G` in a component with the actual conjugate of that component's inclusion.

`affineParabolicQuotientFamilies_injective` derives injectivity of each component
family from the published full-normalizer quotient-chart theorem and the actual
self-normalization theorem for affine-base parabolics.
`finiteAffineParabolicChart_mono_of_disjoint` applies the coproduct injectivity
criterion in the companion module: equality between values from components on
a test scheme must imply equality of indices or emptiness of that test scheme.
This is an explicit additional premise. The module does not prove that a supplied
finite family exhausts the parabolic types or that its chart represents the
presheaf.

All content is internally derived from the imported Library constructions and
the finite coproduct geometry. No new claim is attributed to the original
literature.
