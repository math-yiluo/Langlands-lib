# Integral root points outside higher-multiple root groups

This internal construction works in arbitrary universe over a Henselian local
domain with specified fraction field and algebraically closed residue field.
The data are a relative-component model, a compatible split integral torus,
and an actual special-fibre quotient satisfying `IsReductiveQuotient`.

Suppose the canonical specialization of a generic character `a` is an actual
relative root of the supplied reductive quotient. For each natural number
`n ≥ 2`, `exists_integral_root_point_outside_nsmul` produces an integral section
whose generic point belongs to the original `a` root group. Its actual quotient
reduction belongs to the specialized `a` root functor and lies outside the
`n`-multiple root functor. Its generic point also lies outside the original
`n • a` root group. `integralRootPointOutsideMultiple` chooses the section with
all four properties in its subtype.

The proof first uses `RelativeRoot.exists_rootPoint_not_mem_nsmul` to choose
a quotient-root rational point outside the higher-multiple root functor.
Smoothness of the quotient is supplied by its reductive-quotient predicate;
the acting special-fibre torus is split by base change. Then
`exists_integral_root_quotient_lift` provides an integral generic-root section
with that exact quotient reduction. If its generic point belonged to the
higher-multiple root group, `quotient_reduction_mem_rootFunctor` would put its
quotient reduction in the excluded functor. The canonical character
specialization preserves natural multiples, giving the contradiction.
Nonvanishing of the multiple follows from the torsion-free characters of
the split special-fibre torus.

The provenance is this composition of the named root-point, integral lifting,
and reduction interfaces. There is no additional original-literature assertion.
The construction retains the actual quotient exclusion required by ordinary
root-depth arguments. It does not assert strict-depth quotient vanishing,
identify an affine root depth, or prove the facet-root survival criterion.
