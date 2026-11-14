# Ordinary facet derivatives and actual quotient roots

This internal supporting unit proves the converse to
`UnramifiedQuotientFacetRoots` and combines the two implications into an exact
root comparison. All objects are in an arbitrary universe `u` over a
nonarchimedean local field `F`. The ambient group is affine and carries supplied
parahoric building data `P`, its apartment axioms and its root reflections.

The supplied model `D` has its maximal-unramified integral points characterized
by the zero subgroup intersected with the pointwise fixer of the image of the
translated apartment subset `Fa`. The comparison map `e` is injective and
equivariant. The subset is nonempty; no stronger facet condition is required.
`T` is a closed split integral torus with generic inclusion `P.i` followed by
the actual inner automorphism associated to `g`. `Q` is the actual reductive
quotient of the neutral special fibre. The actual generic reductivity and
maximal split torus come from `P`. Throughout, the universe-`u` proposition
`IntegralOppositeFactorsStatement` is an explicit premise, not a conclusion.

The factorization theorem
`affineRootGroup_subset_strict_mul_double_of_quotient_comparison` first retains
two supplied comparisons: equality of the actual quotient root functor of a
character and its double, and equality of the intrinsic generic doubled root
group with the building's conditional doubled-root convention. Let `ψ` have
derivative an actual root and vanish on `Fa`. For every point of its whole
depth group, descended integrality supplies an actual integral section `x`.
The quotient comparison puts its reduction in the doubled root functor.
Perfect-residue integral lifting supplies an integral section `y` in that
actual generic doubled root group with the same quotient reduction.
Local-field Henselianity is supplied by `henselianLocalRing_integer`; residue
perfection is inferred for the local-field residue field.

The inverse conjugate `w` of the generic point of `y` lies in the original
root group, since the doubled root subgroup is contained in it. Its conjugate
is integral, so the integral/root-fixer equivalence and a point of `Fa` put
`w` in the same whole depth group. The integral section `x * y⁻¹` reduces to
one. The exact facet root reduction kernel places its generic point in the
conjugated strict depth group. Pulling this point back and multiplying by `w`
gives the required factorization into strict depth and the actual conditional
doubled root group. The proof uses the actual monomorphism of the inner
automorphism to check this equality.

`quotient_root_of_mem_facetDerivativeRoots` discharges both comparison premises
if the specialized character is assumed absent from the quotient roots.
Injectivity of the root forms for the split torus identifies the root appearing
in the ordinary affine-root witness with its specified derivative. The
published relative root system theorem applies to the original inclusion and
its conjugate. `IntegralRootDoubleComparison` then gives the all-test quotient
comparison and the generic intrinsic/conditional doubled-root comparison.
The factorization contradicts precisely the noncontainment in the definition
of this same ordinary affine root. Thus the specialized derivative is an
actual quotient root; its character and root length are unchanged.

`quotient_root_iff_mem_facetDerivativeRoots` combines this converse with the
imported quotient-to-facet implication.
`mem_quotient_roots_iff_inverse_specialization_mem_facetDerivativeRoots` expresses
the same equivalence in the special-fibre character lattice.
The entry definition `facetDerivativeRootQuotientEquiv` restricts the canonical
additive character specialization to a bijection between the derivative-root
subtype and the actual quotient-root subtype. Its character formula is
reflexive. This is an internal composition of the named support, lifting,
root-kernel and root-system results; it asserts no new original-literature
formulation. It proves no coroot comparison, full host root datum, or
unconditional opposite-factor statement.
