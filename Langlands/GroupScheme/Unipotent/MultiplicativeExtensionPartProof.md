# The unipotent part of an extension of a multiplicative group: proof

Author: Worker 603 (Task 7802), with the case (a) splitting modules of
Worker 60 (Task 7805).

`Langlands.GroupScheme.multiplicativeExtensionUnipotentPart` proves exactly
the published statement
`Langlands.GroupScheme.MultiplicativeExtensionUnipotentPartStatement.{u}`
(Milne 2017, Notes 16.8 and 16.10) in every universe `u`, with no further
hypotheses: for every field `k`, affine group scheme `G` locally of finite
type over `Spec k`, closed subgroup `i : U ⟶ G` with `U` unipotent and normal
range, and fppf quotient `q : G ⟶ M` by that range with `M` of
multiplicative type,

1. `range i` is contained in the range of every normal closed subgroup
   admitting an fppf quotient onto a group of multiplicative type;
2. for every field extension `K` of `k`, `U_K` is unipotent and its range
   contains that of every unipotent closed subgroup of `G_K`;
3. `U` is smooth if `G` is smooth;
4. `U` is connected if `G` is connected.

## Proof

The theorem applies
`multiplicativeExtensionUnipotentPart_of_algClosedSplitting` from
`Langlands.GroupScheme.Unipotent.MultiplicativeExtensionPartReduction`, whose
only premise `MultiplicativeExtensionUnipotentPart.AlgClosedSplitting` is the
algebraically closed case of Milne's splitting theorem 16.26(a). The premise
is supplied by
`TrigonalizableExtensionSplit.exists_section_of_isAlgClosed` from
`Langlands.GroupScheme.Trigonalizable.ExtensionSplitAlgClosed`, which has
exactly the premise's hypotheses and conclusion.

The reduction module's Markdown describes the proofs of the four parts:
parts 1 and 2 use the published Milne 14.16–14.18 proof
`unipotentMultiplicativeTriviality` and base change of unipotence, closed
subgroups, normality and fppf quotients; parts 3 and 4 use the section over an
algebraic closure `K` of a splitting field of `M` to make `U_K` a scheme
retract of `G_K` (`g ↦ g · s(q(g))⁻¹`), pass smoothness and connectedness to
the retract, and descend them from `K` to `k`.

The splitting modules (`Trigonalizable/StableFlag`,
`Trigonalizable/TriangularEmbeddingWithDiagonalKernel`, `Trigonalizable/ExtensionSplitAlgClosed`,
each with its own Markdown) construct a closed embedding of `G` into the
upper triangular group whose diagonal kernel is `range i` (Milne 16.2), a
character-linear kernel tower of `q` (16.21), and the homomorphic section over
an algebraically closed field (16.26(a)) by the published
`LinearKernelTower.sectionExistence`. They do not prove cases (b) and (c) of
`TrigonalizableExtensionSplitStatement`, and this theorem does not use them.

The Lean check reports the axioms `propext`, `Classical.choice` and
`Quot.sound` only.

## Source

J. S. Milne, *Algebraic Groups* (2017), `milne-2017-algebraic-groups`, SHA256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`: Notes 16.8
and 16.10, printed p.326; Theorem 16.26(a), printed pp.332–333. The
correspondence with the statement is recorded in
`Langlands/GroupScheme/Unipotent/MultiplicativeExtensionPartStatement.md`.
