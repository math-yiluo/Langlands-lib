# Proof of the actual adelic algebra colimits over a fixed initial base

The theorem `adelicFixedModelAlgebraColimit` proves the exact target
`AdelicFixedModelAlgebraColimitStatement` for both actual arithmetic systems,
in an arbitrary common universe. This is an internal coefficient step for
Conrad's equation (3.5.1), with the scope and source recorded in the target's
Markdown. It proves an algebraic universal property and makes no further
claim about points or topologies.

For each fixed finite `S`, replace the usual finite-level cover by the levels
at `S` union `T`. It is monotone, and the published finite-exceptional-set cover
shows that it still covers the actual full adele ring. A test algebra cocone
provides compatible ring maps on these levels. The published
`SubringCover.desc` constructs their unique descended ring map. Its evaluation
formula and cocone naturality show that it agrees with every original stage,
including stages indexed by an arbitrary finite superset of `S`.

For each scalar in the outside-`S` integer ring, apply that stage formula to its
image at the initial level `S`. Since the cocone component is an algebra map,
this proves that the descended ring map commutes with the original scalar
maps, hence is a fixed-base algebra morphism. These morphisms supply the
`IsColimit.desc` field. The stage formula supplies `fac`. For `uniq`, put each
full adele in an enlarged finite level, evaluate the proposed factorization
there, and use the same formula. The two proofs use the actual curve-place and
full number-field coefficient rings, respectively. Every infinite number-field
factor remains present. No finite constants, perfectness, function-field
presentation or nonempty initial set is used.
