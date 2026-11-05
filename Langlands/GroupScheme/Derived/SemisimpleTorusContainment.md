# Split tori with actual semisimple root data lie in the derived subgroup

Author: Worker 1484.

This module proves containment in the full scheme-theoretic derived subgroup,
conditional only on a supplied actual root datum. It does not assume or prove
the existence of that root datum.

`IsRootDatumOf.range_le_derivedSubgroup_of_finite_corootIndex` concerns a split
torus `i : T.toGrp ⟶ G` in an affine group over any field. The underlying
morphism of `i` is monic. An actual root datum `P` of `i` is supplied and
the quotient of its cocharacter lattice by its coroot span is finite. The
conclusion is `SubgroupFunctor.range i ≤ derivedSubgroup G`.

For each actual closed subgroup `j` containing the commutators, the preceding
`SplitTorusCommutators` module places every coroot in
`cocharactersLandingIn i (SubgroupFunctor.range j)`. Hence that submodule
contains the coroot span. Each element of the finite quotient has finite
additive order, so a positive integer multiple of each cocharacter belongs
to the coroot span. The fpqc saturation theorem removes this integer
multiple. Thus every cocharacter lands in `range j`, and the coordinate
decomposition of a split torus puts its entire range there. Testing every
such `j` is exactly membership in `derivedSubgroup G`.

`IsSemisimple.range_torus_le_derivedSubgroup_of_rootDatum` discharges the
finite-coroot-index premise for a semisimple group and a closed split
torus with a supplied actual root datum. It uses the published necessity
theorem `IsSemisimple.finite_quotient_rootSpan` and the published lattice
duality theorem `RootPairing.finite_quotient_rootSpan_iff_corootSpan`.
Smoothness of the ambient group and splitness of the torus supply finiteness
of the root index set and finite generation of the character lattice.

`SemisimpleRootDatumTorusDerivedStatement.{u}` packages this last assertion
in arbitrary universe `u`, and `semisimpleRootDatumTorusDerived` proves it.
The statement retains every field and every test scheme, with no
characteristic restriction. The supplied root datum need not be reduced,
and the supplied closed torus need not have an additional maximality
certificate.

These are internal consequences of the named published definitions and
lemmas, composed with `SplitTorusCommutators`. They isolate the part of
semisimple perfectness that follows from actual reflection representatives
and finite lattice index. The full arbitrary-field perfectness statement
still requires actual root-datum existence and a generation argument for
the ambient group.
