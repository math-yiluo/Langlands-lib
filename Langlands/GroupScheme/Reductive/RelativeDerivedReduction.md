# Reductions for the relative derived group

`RelativeDerivedReductionStatement` states that
`RelativeDerivedGroupExistenceStatement` and
`RelativeSemisimpleFppfPerfectStatement` together imply the unchanged
`RelativeDerivedGroupStatement`, uniformly in the universe. The theorem
`relativeDerivedGroup_of_inputs` proves this implication. This module
does not prove either input or the unconditional derived-group theorem.

This is an internal reduction from the published statements and constructions
in the Library. `RelativeDerived.IsAdmissible` and
`RelativeDerived.LocallyCommutator`, imported from `RelativeDerivedInputs`,
are the exact predicates appearing locally in the unchanged target. The
reduction introduces no further hypothesis on the base, the group, the test
scheme, or the quotient.

`isSemisimple_residueFiber` reflects semisimplicity of the geometric fibre
along the field extension from a residue field to its algebraic closure.
`IsReductive.isSemisimple_baseChange` then treats every field-valued point
of the base. It factors that point through its residue-field point, pulls
back the finite-centre property of the semisimple residue fibre, and combines
it with the published connected-reductivity result at arbitrary field-valued
points. The composition isomorphism identifies this group with the requested
pullback.

`RelativeDerived.IsAdmissible.baseChange` proves stability of admissibility
under every scheme base change. Closedness, normality of the all-test range,
reductivity, the relative-torus property, and the fppf quotient condition use
their published base-change lemmas. The field-valued result above supplies
semisimplicity at the geometric points of the new base. This argument
requires neither of the two geometric input propositions.

The remaining helpers assume relative semisimple fppf-perfectness.
`IsAdmissible.locallyCommutator_of_mem_range` lifts a point of the range to
the admissible subgroup, applies perfectness there, and maps the local
commutators into the ambient group. Conversely,
`IsAdmissible.mem_range_iff_locallyCommutator` applies a supplied quotient
to a locally commutator point when the quotient target is commutative.
The published annihilation lemma and fppf-cover hom ext show that its image
is the identity; equality of the quotient kernel range with the subgroup
range gives membership.

`IsAdmissible.range_iff_locallyCommutator` chooses the relative-torus quotient
provided by admissibility and uses the published theorem
`RelativeTorus.IsTorus.isCommMonObj`. Thus an admissible range is intrinsically
the local commutator functor. `IsAdmissible.range_eq` compares this
characterization on every test scheme to prove equality of any two
admissible subgroup functors. The uniqueness conclusion is equality of
their all-test ranges, exactly as in the target.

`IsAdmissible.kernel_comp_eq_zero` proves that every homomorphism to a
commutative group kills the scheme kernel of any fppf quotient by the
admissible range. The kernel inclusion itself belongs to that range, so it
is locally commutator and its composite is the identity. The helper
`IsAdmissible.existsUnique_factor` supplies flatness, surjectivity and local
finite presentation from the quotient predicate, then applies
`FppfHomDescent.existsUnique_hom`. The quotient in this conclusion is
arbitrary; its target need not be the torus chosen earlier. No
quasi-compactness assumption is used.

Finally, `relativeDerivedGroup_of_inputs` chooses an admissible subgroup
using the existence input. It supplies uniqueness by `range_eq`, the
commutator-sheaf characterization by `range_iff_locallyCommutator`,
arbitrary-base-change admissibility by `baseChange`, and the universal
property by `existsUnique_factor`. Unfolding the named input predicates
matches the target's local formulas definitionally.
