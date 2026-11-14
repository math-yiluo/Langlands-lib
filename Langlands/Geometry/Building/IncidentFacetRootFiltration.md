# Positive root filtrations of incident facets

This internal unit derives filtration comparisons for two actual apartment
facets `F`, `C` with `F` a face of `C`. The upper facet need not be a chamber.
The universe of the underlying field is arbitrary.

For general `KPApartmentData i ω`, AS4 is an explicit hypothesis: every extended
affine root is an affine root, or its double is an affine root.
`rootFixer_comparison_of_incidentFacets` states that
`rootFixerPlus a F ≤ rootFixerPlus a C` and
`rootFixer a C ≤ rootFixer a F`. The proof writes each root fixer as the
depth-zero filtration at a point of its facet, then uses the published
filtration comparison along formal facet closure.

`rootFixer_eq_of_incidentFacets_of_nonneg` assumes that a root is nonnegative
on the displacement from a point `y` of `F` to a point `x` of `C`. The
filtration shift formula makes the depth-zero filtration at `y` a subgroup
of the one at `x`. The preceding reverse inclusion gives equality of the
nonstrict root fixers.

With connected reductivity of `G` and maximal splitness of `i`,
`exists_genericCocharacter_rootFixer_eq_of_incidentFacets` gives a generic
cocharacter `ν` such that every relative root positive on `ν` has the same
nonstrict root fixer on `F` and `C`. It lifts `x -ᵥ y` to `V(S)` and uses
the published
`exists_genericCocharacter_eval_nonneg_of_isMaximalSplitTorus` to choose
`ν` adapted to that displacement. This ensures the nonnegativity required
by the previous lemma. No full affine-root-system hypothesis or supplied
facet positive-system condition is required.

If both facets are bounded under all real affine functionals,
`exists_genericCocharacter_filtrationDepth_eq_of_incidentFacets` expresses
the same equality at any common reference point `z`, using the actual
`rootFixerDepth` for each facet. It asserts equality of filtration
subgroups, not equality of their real depth parameters.

The two existence declarations in namespace `IntegerValuationBuildingData` specialize
these existence results to actual integer-valued building data. The
published `affineRoot_mem_or_two_smul_mem` theorem supplies AS4, and the
data supply connected reductivity and maximal splitness. Boundedness
remains explicit for the depth version.

`IntegerValuationBuildingData.incidentFacetCocharacter` chooses a
cocharacter from the integer-valued root-fixer existence theorem. Its
genericity and the equality of nonstrict fixers for every positive relative
root are proved by `incidentFacetCocharacter_isGeneric` and
`rootFixer_eq_of_incidentFacetCocharacter_pos`, respectively. Under the
same boundedness hypotheses as above,
`filtrationDepth_eq_of_incidentFacetCocharacter_pos` gives equality of the
actual filtration subgroups for this single chosen cocharacter at every
reference point. The choice depends only on the building data and the
incident facets with their facet and incidence proofs; boundedness and a
reference point are not inputs to the choice. There is no asserted
uniqueness or canonical geometric characterization of the chosen
cocharacter.

The provenance is derived from the imported facet-constancy,
facet-closure, filtration-shift, generic-cocharacter and bounded-fixer
theorems. This unit concerns apartment root groups. It does not construct
integral root models, identify residue-root subgroups, or prove
parabolicity of a special-fibre image.
