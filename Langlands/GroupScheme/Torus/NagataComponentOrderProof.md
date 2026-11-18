# The finite-component necessity in Nagata's theorem

`Langlands.GroupScheme.nagataComponentOrderNecessity` proves exactly the
published `NagataComponentOrderNecessityStatement.{u}` in every universe,
with no additional hypotheses. For every field `k` of nonzero characteristic
`p` and every affine locally finite-type group scheme `G`, the task's exact
all-affine-test finite-coordinate linear-reductivity condition implies
that `p` does not divide the `Nat.card` of its geometric connected components.
No smoothness, reducedness, perfectness or algebraic-closure assumption is
imposed on `G` or `k`.

The published independent theorem
`LinearReductivity.linearlyReductiveFieldExtension` carries linear
reductivity to the actual base change of `G` to the chosen algebraic closure.
Its proof uses local normalized right integrals and tensor transfer in both
directions, independently of Nagata's classification.

The published canonical component regular construction over that algebraic
closure now applies. It uses the normal quotient of rational sections by
those in the actual identity component, whose order is the number of
geometric components. Its regular representation is an actual finite matrix
representation: the morphism and its stability identities are glued on the
actual open component schemes, retaining nonreduced tests. Linear reductivity
makes this representation semisimple, and the elementary finite regular
representation obstruction forces its order to be prime to `p`. The exact
cardinal comparison supplies the required `Nat.card` conclusion. The Lean
proof applies the published theorem
`not_dvd_card_geometricComponents_of_baseChange_linearlyReductive` and
supplies its base-change reductivity premise using the field-extension theorem.

All supporting mathematics is imported from the published Library. The target
statement and all pairs in its import closure are unchanged. The only axioms
used are `propext`, `Classical.choice` and `Quot.sound`.

This proves the component-order necessity only. The identity-component
multiplicative-type necessity and the sufficiency direction are separate
parts of the full Nagata theorem.
