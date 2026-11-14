# Root survival in the actual reductive special-fibre quotient

This internal supporting construction concerns a supplied relative-component model
pair `D` over an arbitrary local domain `R` with fraction field `K`, its actual
neutral special fibre, and a supplied `SpecialFibreQuotientData D`. All types live
at arbitrary universe `u`. The hypothesis `Q.IsReductiveQuotient` asserts that the
specified radical is a represented smooth connected normal unipotent closed
subgroup, that the specified projection is its actual represented fppf quotient,
and that the target is connected reductive. No quotient existence is asserted.

For a supplied `IntegralTorusData D S i`, assume only that its integral torus is
split. Write `t = T.specialFibreInclusion`, `q = Q.projection`, and `k` for the
residue field of `R`. Closedness and maximality of `t` are not needed for these
weight identities; in particular the full torus clause is not an extra premise.
Here `relativeRoots` has its published meaning: nonzero characters with nonzero
adjoint weight space.

The module proves the following statements on these actual maps:

- `projection_smooth`: the quotient projection is smooth.
- `ker_projection_eq_radical_lie`: the kernel of `Lie.targetMapLinear q k` is
  exactly `(SubgroupFunctor.range Q.radicalInclusion).lie k`.
- `map_weightSpace_eq`: the differential maps the entire `χ`-weight space for
  `t` onto the `χ`-weight space for `t ≫ q`, for every character including zero.
- `weightSpaceQuotientEquiv`: the source weight space modulo the kernel of
  the restricted differential is linearly equivalent to the target weight space.
- `weightSpace_eq_bot_iff_le_radical_lie`: the target weight space vanishes
  exactly when the entire source weight space lies in the radical's tangent
  image.
- `mem_relativeRoots_iff_not_le_radical_lie`: `χ` is a quotient root exactly when
  `χ ≠ 0` and its source weight space is not contained in that tangent image.
- `relativeRoots_subset_specialFibre`: every quotient root is already a root
  for the same torus in the neutral special fibre.

The proof of smoothness applies the published
`RelativeRoot.IsFppfQuotient.smooth_of_smooth_kernel` to the actual radical
inclusion. Its closed immersion represents its own all-test range, and its
smoothness is a field of the radical predicate. Quasi-compactness of the
projection follows from the affine source and its structural morphism, using
`QuasiCompact.of_comp`.

The tangent-kernel identity specializes the published
`lie_range_kernelι_eq_ker_targetMapLinear` and rewrites the scheme-theoretic
kernel range using the supplied fppf quotient equality. This is an equality of
actual tangent submodules, rather than an equality inferred from rational point
kernels.

Functoriality maps a source weight vector to the same target weight. In the
opposite direction, smoothness gives a preimage under the full differential by
`Lie.targetMapLinear_surjective_of_smooth`. Splitting of the special-fibre torus
follows by base change from the integral torus. The published
`Lie.exists_weightSpace_preimage` then chooses a preimage of the same character
weight. Local finite type of the source comes from the integral model by base
change, and that of the target follows from its connected reductivity and hence
smoothness.

The surjective restricted differential also gives the explicit linear
equivalence `weightSpaceQuotientEquiv` by
`LinearMap.quotKerEquivOfSurjective`.

Finally, `LinearMap.le_ker_iff_map` turns vanishing of the image weight space into
containment in the differential kernel. The exact kernel identity gives the
radical criterion, and the definition of `relativeRoots` gives the root
criterion. If the source weight space were zero it would lie in the radical
image, so the criterion also proves the stated root inclusion.

The provenance is the indicated composition of published geometric and linear
algebra results. This module does not identify either root set with derivatives
of affine roots vanishing on a facet, compare coroots, or prove
`UnramifiedFacetRootDatumStatement`. Those geometric comparisons remain separate
obligations of Task 6218.
