# Connected groups act trivially on groups of multiplicative type: proof

`Langlands.GroupScheme.multiplicativeTypeConnectedAction` proves the unchanged
[`MultiplicativeTypeConnectedActionStatement`](MultiplicativeTypeConnectedActionStatement.md)
for every universe `u`. For a field `k`, a connected group scheme `G` of finite
type over `k`, and a group `H` of multiplicative type, it proves both that every
`AutomorphicAction G H` is trivial on points over every test scheme and that
every closed normal inclusion `H ⟶ G` is central.

The Lean proof applies the published theorem
`multiplicativeTypeConnectedAction_of_diagonalizableRigidity` from
[`MultiplicativeTypeConnectedActionReduction`](MultiplicativeTypeConnectedActionReduction.md)
to the published proof `diagonalizableRigidity` from
[`DiagonalizableRigidityProof`](DiagonalizableRigidityProof.md). Thus its type is
exactly `MultiplicativeTypeConnectedActionStatement.{u}`, with no remaining
rigidity assumption or additional hypotheses. This module adds only that theorem.

The reduction chooses a field extension splitting `H`, retains connectedness of
`G` after this extension using geometric connectedness of connected algebraic
groups, and applies diagonalizable rigidity to the action with parameter scheme
`G`. The identity of `G` supplies the constant value. Flat surjective reflection
then descends triviality to `k` on every scheme test. For a closed normal subgroup,
the reduction constructs its conjugation action, applies triviality, and obtains
centrality after every refinement required by the Library's centre functor.

The imported rigidity proof uses orthogonal idempotent coefficients of group-like
coordinate expressions, clopen loci on the connected parameter scheme, and
agreement on affine covers. It covers diagonalizable groups with torsion character
groups and retains equality on nonreduced test schemes. The acting group in the
conclusion is any connected group scheme of finite type; it need not be affine
or smooth, as explained in the unchanged statement Markdown.

The mathematical source is James S. Milne, *Algebraic Groups* (2017), registered
as `milne-2017-algebraic-groups`: Corollaries 12.37 and 12.38, printed page 244,
following Theorem 12.36, printed pages 243–244. The two corollaries follow from
family rigidity and conjugation, respectively. The statement Markdown explains
the extension from Milne's affine convention for algebraic groups to the Library's
parameter scheme scope. The final composition and its imported reduction use
that same route; the imported rigidity proof uses the alternative coefficient
argument described above. The target's Lean and Markdown pair and all its imports
are unchanged.
