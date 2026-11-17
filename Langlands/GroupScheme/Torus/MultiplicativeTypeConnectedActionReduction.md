# Connected multiplicative-type actions: a reduction to diagonalizable rigidity

This internal support module reduces the unchanged published
`MultiplicativeTypeConnectedActionStatement` to the unchanged
`DiagonalizableRigidityStatement`. The reduction is conditional on the latter
proposition; it does not supply its proof.

The mathematical source is J. S. Milne, *Algebraic Groups* (2017),
Corollaries 12.37–12.38, printed page 244, following Theorem 12.36 on page 243
(registered source `milne-2017-algebraic-groups`). The registered errata snapshot
was read: its correction to Proposition 12.41 does not change these results.
The auxiliary constructions and descent lemmas are internal consequences of
the Library's actual group-scheme and pullback interfaces.

`AutomorphicAction.ofNormalSubgroup` constructs conjugation by the ambient
group on a normal subgroup represented by a monomorphism. It uses the existing
normalized-conjugation construction and proves that composition with the
inclusion equals ambient conjugation on every scheme test. Triviality of
this action implies `IsCentral`, including every refinement in the centre's
definition.

`AutomorphicAction.act_eq_self_of_baseChange` reflects triviality across a
flat surjective base map. For a test scheme it pulls back the test along the
base map, transports both points through `baseChangePointsEquiv`, and uses
naturality of the action. The test projection is an epimorphism because it
is flat and surjective, so equality descends. The test scheme and target
need not be affine or reduced.

For a diagonalizable target, the rigidity proposition applies directly to
the action morphism with parameter scheme the acting group. Its fibre at
the identity is the identity map by the action law. For a multiplicative-type
target the proof chooses the field extension and actual diagonalizable
isomorphism from `IsMultiplicativeType`. The published
`connectedSpace_baseChange_of_connected` keeps the acting group connected,
and local finite type and quasi-compactness persist by base change. Field
extensions are flat and surjective, so the preceding reflection lemma
returns triviality over the original field.

The final theorem combines action triviality with the normal-subgroup
conjugation construction. Its hypotheses are exactly the two published
propositions: no smoothness, affineness, perfectness or characteristic
restriction is added. The statement's Lean and Markdown files and their
imports are unchanged.
