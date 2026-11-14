# Specializing integral torus normalizers

Let `R` be a domain with fraction field `K`, let `D` be a supplied
relative component model, and let `T : IntegralTorusData D S i`. The first
construction assumes that the integral torus is split. Every automorphism
`σ` of its specified generic torus `S` has an integral extension
`T.integralAutomorphism hT σ`, and
`integralAutomorphism_generic_comm` proves its compatibility with the
given generic-fibre isomorphism.

The construction descends both the generic automorphism and its inverse.
Bijective generic character base change supplies character surjectivity;
`IsSplitTorus.hom_baseChange_surjective_of_characterSurjective` then
descends the actual homomorphisms. Character extensionality and injective
character base change reflect the two inverse identities. Transport by
`T.genericIso` gives `exists_integralAutomorphism`, and classical choice
selects an extension with the proved compatibility square. No assertion
that a generic torus point extends to an integral point is used.

Assume further that `R` is local. The definition
`T.specializedAutomorphism hT σ` is the residue base change of this
constructed integral extension, on `T.specialFibre` itself.
`characterSpecialization_characterAut` proves that its character action
commutes with the canonical generic-to-special character specialization.
Here `characterAut σ χ = σ.inv ≫ χ`, matching the published Weyl-action
convention. The proof derives the generic square for the inverse,
uses `characterLattice.baseChange_precomp`, and represents every generic
character by an actual integral character.

The theorem `characterAut_specialized_reflection` specializes any supplied
generic reflection formula

`characterAut σ χ = χ - latticePairing S χ ν • a`.

For every special character its result is the same formula with the
specialized root `T.characterSpecialization hT a` and the matching coroot
`T.cocharacterSpecialization hT ν`. This uses
`T.latticePairing_specialization`, so both lattices come from the same
integral torus and the integer coefficient is preserved.

For normalizer specialization, let `T.IsClosedSplit` hold and take an
actual section `x : D.neutral.integralSections` whose generic point
normalizes `i` through `σ`. The theorem `isNormalizingPoint_integral`
proves that `x` normalizes `T.inclusion` through the constructed integral
automorphism. Its proof first checks the generic normalizer square,
using `T.generic_comm`, `integralAutomorphism_generic_comm`, compatibility
of inner automorphisms with base change, and naturality of inner
automorphisms under `D.neutral.genericIso`. Splitness makes the source
torus smooth and hence flat. The target model is affine and hence
separated. The published
`Langlands.AbelianScheme.genericFibre_map_injective` therefore reflects
the square to the integral base.

The theorem `isNormalizingPoint_reduction` changes this actual square to
the residue field. For any supplied `Q : SpecialFibreQuotientData D`,
`isNormalizingPoint_quotient` then constructs the normalizer square for
`T.specialFibreInclusion ≫ Q.projection`, with the explicit quotient point
`rationalPoints.map Q.projection (D.neutral.reduction x)` and
`T.specializedAutomorphism hT.1 σ`. Naturality of inner automorphisms
under `Q.projection` proves this final step. It requires neither
surjectivity on rational points nor the reductive-quotient validity
predicate.

This is derived content from the published split-torus character,
homomorphism base-change, generic-rigidity, inner-automorphism and lattice
pairing results. It supplies the algebraic specialization of an actual
integral normalizer and its reflection formula. It does not establish
that the required facet reflection representatives are integral, identify
the quotient roots, or prove `UnramifiedFacetRootDatumStatement`.
