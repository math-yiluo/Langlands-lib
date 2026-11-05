# Perfect rational points and the scheme-theoretic derived subgroup

This is an internal derived helper for the semisimple-perfectness proof. Its
provenance is the composition of the published closed-subgroup containment
criterion with Mathlib's abstract commutator results. It does not assume any
unproved structural statement about reductive groups.

All declarations retain arbitrary universe `u`. Let `k : Type u` be an
algebraically closed field and `f : H → G` a homomorphism of actual group schemes
over `Spec k`. Suppose that the underlying scheme of `H` is reduced and locally
of finite type over `k`. If the abstract group `H(k)` is perfect, then
`range_le_derivedSubgroup_of_rationalPoints_perfect` proves that the full
test-scheme range functor of `f` is contained in `derivedSubgroup G`. No
reducedness, finite-type, affineness, smoothness or representability assumption
is imposed on the target group `G`.

`RationalPerfectnessCriterionStatement` is the Prop-valued definition of this
criterion, universally quantifying the field, both group schemes and the
homomorphism with precisely these hypotheses. The theorem
`rationalPerfectnessCriterion` proves it by the range-containment argument below.
This named criterion is an internal auxiliary result; it has no semisimplicity
hypothesis and does not prove the semisimple-perfectness target.

For each closed subgroup `i : K → G` containing all commutators, pull back its
subgroup of rational points along `H(k) → G(k)`. Functoriality of commutators
shows that this pullback contains the abstract commutator subgroup of `H(k)`,
so perfectness makes it the whole group. The published
`SubgroupFunctor.range_le_of_algClosed_points` promotes this rational-point
containment to containment of full range functors. Intersecting over all such
closed subgroups gives the desired inclusion. Applied to the identity
homomorphism, this proves
`derivedSubgroup_eq_top_of_rationalPoints_perfect`.

The two remaining lemmas give a concrete abstract rank-one input.
`commutator_sl2_eq_top_of_isAlgClosed` applies
`Matrix.SL2.commutator_eq_top` from Mathlib's
`LinearAlgebra/Matrix/SpecialLinearGroup.lean`. An algebraically closed field is
infinite; choosing a scalar outside `{0, 1, -1}` supplies `a ≠ 0` and `a² ≠ 1`.
Mathlib proves its theorem by expressing transvections as commutators with
`diag(a, a⁻¹)` and generating every determinant-one matrix by transvections.
This applies in every characteristic, including characteristic two.

Finally, `derivedSubgroup_eq_top_of_sl2_rationalPoints` takes an explicit
multiplicative equivalence from the actual matrix group `SL₂(k)` to `G(k)`.
It transfers abstract perfectness along that equivalence using
`map_commutator_eq` and then applies the rational-point criterion. This
conditional corollary constructs no `SL₂` group scheme and supplies no
equivalence for an existing scheme: those constructions remain prerequisites
of a scheme-level rank-one application. The conclusions are full
test-scheme subgroup-functor equalities, including on nonreduced tests; the
argument uses reducedness of the source group scheme to obtain them.
