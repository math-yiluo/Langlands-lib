# Nested dynamic decompositions from actual-root structural targets

This internal conditional assembly keeps
`RelativeRootSignInclusionsStatement` and `RelativeRootNegationStatement`
as explicit hypotheses. It does not prove either structural proposition or
the unconditional `DynamicNestedParabolicDecompositionStatement`.
All declarations are uniform in the original universe and retain arbitrary
fields, connected reductive groups and every test scheme.

`Dynamic.unipotent_le_of_parabolic_le_of_rootSigns` proves reverse radical
containment for two cocharacters of one maximal split torus. Write the
cocharacters as `zeta` and `eta` and assume `P(zeta) ≤ P(eta)`. The first
conjunct of the sign-inclusion hypothesis says that every actual root
nonnegative on `zeta` is nonnegative on `eta`. Given a root `α` positive
on `eta`, suppose it is nonpositive on `zeta`. The negation hypothesis
makes `-α` an actual root, nonnegative on `zeta`; hence it is nonnegative
on `eta`. Bilinearity of the lattice pairing contradicts the strict
positivity of `α` on `eta`. Thus positive root support for `eta` is
contained in that for `zeta`. The second conjunct of the sign-inclusion
hypothesis gives `U(eta) ≤ U(zeta)` as subgroup functors, on every test.
No centralizer inclusion is used in this step.

`DynamicNestedParabolicDecompositionFromRootSigns` is the proposition that
these two structural hypotheses imply the exact published nested target.
The theorem `dynamicNestedParabolicDecomposition_of_rootSigns` proves it.
For a compatible nested pair, unpack its common maximal split torus and
the two realizing lattice cocharacters. Apply the preceding radical
containment lemma and then
`Dynamic.nestedLeviDecomposition_of_inclusions` to the supplied parabolic
and centralizer inclusions. This gives the normal complement and all three
ordered set-product equalities on every test scheme, including nonaffine
and nonreduced tests.

The provenance is an internal implication between the published targets,
using the published lattice pairing and the elementary dynamic limit
calculations in `Dynamic.NestedDecomposition`. Worker 1107 supplied the
root-negation argument; Worker 1291 formalized and assembled it. The
independent owners of the two structural targets, standard cocharacter
realization, standard parabolic order and centralizer reductivity retain
their proof obligations.
