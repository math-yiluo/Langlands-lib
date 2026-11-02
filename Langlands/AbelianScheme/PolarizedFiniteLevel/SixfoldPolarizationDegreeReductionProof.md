# Conditional native degree of the sixfold polarization

The theorem
`Langlands.AbelianScheme.PolarizedFiniteLevel.sixfoldPolarizationDegreeReduction`
has full type
`Langlands.AbelianScheme.PolarizedFiniteLevel.SixfoldPolarizationDegreeReductionStatement`.
It preserves the actual datum, its dual witness, its polarization and its
native degree convention.

The proof installs the assumed finite and flat properties of the actual
multiplication-by-six map. The existing isogeny in `a.polarized` supplies
finite flatness of `a.polarization`. The dual abelian scheme is locally of
finite type over the noetherian spectrum of the field, so its underlying
scheme is locally noetherian.

`AbelianScheme.hom_comp`, `Preadditive.nsmul_comp` and the identity law prove
that the underlying composite of multiplication by six followed by the
polarization is the underlying morphism of `6 • a.polarization`.
The finite and flat composition instances therefore give the first two
conclusions. The published theorem
`Langlands.AlgebraicGeometry.finiteFlatConstantRankComposition`, applied to
these same two actual morphisms, multiplies the assumed rank `6^(2*g)` by
the rank `d^2` supplied by `a.degree`. Rewriting the composite gives exactly
the asserted `HasConstantDegree` conclusion.

This is an internal specialization of published rank composition and the
datum's existing fields. Finite flatness and the degree of multiplication by
six remain explicit hypotheses. No unconditional multiplication geometry,
ampleness or cohomological conclusion is claimed here.
