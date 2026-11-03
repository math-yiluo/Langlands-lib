# Semigroup reductions for actual-root sign inclusion

Authors: Worker 1312, using Worker 1323's actual-root support conversion.

This internal unit defines `RelativeRootSignInclusionsFromSemigroups` as the
conditional implication

`SemigroupRealizationStatement → DynamicSemigroupComparisonStatement → RelativeRootSignInclusionsStatement`.

The theorem `relativeRootSignInclusions_of_semigroupRealization` proves that
implication. Both structural propositions remain explicit theorem-valued
premises. This is not an unconditional proof of either structural proposition
or of the exact task target `RelativeRootSignInclusionsStatement`. The exact
task still requires independently proved structural inputs with no added
premises in its eventual theorem.

The construction is internally derived from the published definitions and
interfaces in `WeightSemigroupStatement`, the pointwise support-order API in
`WeightSemigroupSupport`, and the actual-root support conversion in
`RelativeRootSignSupport`. The latter converts between the same actual
adjoint roots as the task target and the ambient conjugation-action support;
there is no replacement root datum or assumed root-group decomposition.

For parabolics, `dynamic_parabolic_le_iff_on_weightSupport_of_semigroup`
rewrites both Dynamic functors as nonnegative semigroup subgroups. The
realization proposition supplies the exact Lie image of the source subgroup.
The target subgroup's support bound follows by applying its maximality
equivalence to its own identity inclusion. The support-order helper then
yields the equivalence on actual ambient weights. Its necessity transports
a nonzero tangent vector along the all-test inclusion; its sufficiency
reuses every admissible source generator for the target semigroup.

For unipotent functors,
`dynamic_unipotent_le_of_on_weightSupport_of_semigroup` rewrites both as
strictly positive semigroup subgroups and applies generator monotonicity on
actual ambient support. This direction needs only the dynamic comparison
proposition, because monotonicity does not require exact Lie images.

The final conditional assembly takes a connected reductive group and a
maximal split torus as in the exact target. It uses the group's supplied
smoothness, affineness and connectedness, and the torus's supplied splitness.
For parabolics it composes the ambient-support equivalence with
`nonnegative_rootSupport_iff` in the reverse direction. For unipotent
functors it converts the assumed rootwise positive sign containment by
`positive_rootSupport_iff` and applies the preceding implication.

All subgroup inclusions are of `SubgroupFunctor` on every test scheme. The
original field universe and arbitrary cocharacters are retained. The zero
character imposes no additional condition: it pairs to zero, so the
nonnegative target condition holds and the positive source condition is
false. Empty and nonreduced actual root sets require no separate premise.
No finiteness, genericity, perfectness, characteristic-zero or absolute
splitness hypothesis is added.
