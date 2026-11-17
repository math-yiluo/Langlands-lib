# The relative derived group of a reductive group scheme

Author: Worker 672.

`Langlands.GroupScheme.relativeDerivedGroup.{u}` proves the unchanged
`Langlands.GroupScheme.RelativeDerivedGroupStatement.{u}` for every universe
`u`. For every scheme `S` and reductive group scheme `G` over `S`, it supplies
an admissible closed normal subgroup with semisimple geometric fibres and
a represented fppf quotient that is a relative torus. Every admissible
subgroup has the same all-test range. A point belongs to that range exactly
when it belongs to the abstract commutator subgroup after an fppf cover.
Admissibility is preserved by every base change. Every homomorphism from
`G` to a commutative `S`-group scheme factors uniquely through each fppf
quotient by that range.

The Lean proof applies the published `relativeDerivedGroup_of_inputs` to
the published theorems `relativeDerivedGroupExistence` and
`relativeSemisimpleFppfPerfect`, all at the same universe. The first input
constructs an admissible subgroup over an arbitrary base. The second
asserts that every point of every relative semisimple group is fppf-locally
in its abstract commutator subgroup.

The reduction identifies the range of any admissible subgroup with the
fppf-local commutator functor: perfectness gives one inclusion, and the
commutativity of its torus quotient gives the other. This identifies all
admissible ranges. The reduction also proves admissibility after arbitrary
base change. Finally, local commutators vanish under homomorphisms to
commutative groups, and fppf descent gives the unique factorization through
any supplied quotient by the range.

This is an internal composition of published proofs. Its provenance and
proof route are the stated existence, perfectness and reduction theorems;
it introduces no new definition or literature statement. The target and its
imported Lean/Markdown pairs are unchanged. No hypothesis on the base,
characteristic, splitness, reducedness, noetherianity or quasi-compactness
is added.
