# Open-subgroup embeddings with independent carrier universes

This internal unit applies the published
`Langlands.Induction.openIrreducibleExtension` without requiring the original
subgroup carrier universe to dominate the group universe. It uses the
published carrier lift and its actual representation equivalence.
It introduces no new cyclicity, quotient-existence or ambient-extension
argument.

For an actual open subgroup `H` of a topological group `G : Type uG` and an
actual smooth complex representation `A` of `H` in `Type uV`,
`OpenIrreducibleEmbedding H A` records an ambient smooth irreducible
representation in `Type (max uG uV)`, an actual intertwiner from the original
action of `A` to its restriction, and injectivity of this intertwiner.
The group and original carrier universes are independent.

`openIrreducibleEmbedding` supplies these data when `A` is irreducible.
It lifts `A` to `ULift.{uG} A`, preserving irreducibility through the published
equivalence. The published ambient extension applies to this lifted carrier.
Composing its embedding with the lift equivalence gives an injective
intertwiner defined on the original carrier. The output ambient carrier
remains in `Type (max uG uV)`.

`exists_irreducible_ambient_of_open_subgroup` expresses the same conclusion
for an unbundled smooth complex action. It bundles that action and uses the
chosen construction.

No admissibility, finite index, normality, compact coefficients or
finite restriction decomposition is required. The construction does not
assert ambient cuspidality or a common coefficient-support bound. Those
remain separate obligations in its norm-kernel application.
