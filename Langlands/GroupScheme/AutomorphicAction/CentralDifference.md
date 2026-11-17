# Difference families for actions on central extensions

Worker 302.

This is an internal construction for the central-extension action argument.
Let `j : N ⟶ H` be a monomorphism of group schemes over an arbitrary base `S`,
and let `p : H ⟶ Q` be flat, surjective and quasi-compact, with
`range (kernelι p) = range j`. Suppose an automorphic action `a` of `G` on `H`
fixes the points of `N` and acts trivially after composition with `p`, on every
test scheme.

The morphism `differenceHom a : G × H → H` sends `(g,x)` to
`x⁻¹ a(g,x)`. Triviality on the quotient places this difference in `range j`.
The points equivalence of the represented subgroup factors this actual
morphism through `N`, giving `differenceLift`.

If `p(x) = p(y)`, the point `x/y` lifts to `N` and is fixed by the action.
Writing `x = (x/y)y` shows that both differences are equal. Cancellation of
the monomorphism `j` gives the same equality for `differenceLift`. Effective
epimorphism descent along the fpqc morphism `G × p` produces the actual
morphism `centralDifference : G × Q → N`. Its displayed evaluation formula
recovers `x⁻¹ a(g,x)` after composition with `j`.

The family is natural under all test morphisms and is trivial when `g = 1`.
When `j` is central, its values commute with all points of `H`, and a group
calculation shows that the difference is multiplicative in `x`. The same law
for `centralDifference` follows by lifting each of the two quotient points
locally along `p` and cancelling `j`.

These are derived categorical and group-theoretic constructions, with no
field, finiteness, connectedness or multiplicative-type assumptions. They
formalize the difference-map step in the proof route documented in
[`MultiplicativeTypeExtensionActionStatement`](../Torus/MultiplicativeTypeExtensionActionStatement.md);
they do not assert rigidity or prove that global statement.
