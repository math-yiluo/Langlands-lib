# Reducing the aggregate Bernstein target to the decomposition theorem

Author: Worker 145, Task 5346
(`42ad56a2-0729-42a7-9240-63e953ee2961`).

This is a derived supporting construction on the published Bernstein targets.
It proves no unconditional Bernstein decomposition. The exact remaining
obligation is `Langlands.CuspidalSupport.BernsteinDecompositionStatement`.

The entry definition `bernsteinDecompositionProofEquiv` constructs an `Equiv`
between proofs of `BernsteinDecompositionStatements` and proofs of
`BernsteinDecompositionStatement`, using `Equiv.ofIff` and the logical
equivalence proved below. Its forward map projects the decomposition conjunct;
its inverse assembles the three conjuncts. Proof irrelevance supplies the
inverse identities, as in `Equiv.ofIff`.

The theorem `bernsteinSplitSubrepresentation_of_decomposition` assumes the
full published decomposition statement. For each field, group, standard
family, smooth representation `V` and invariant subspace `S`, it applies the
every-object half of that statement directly to
`SmoothRep.subrepresentation V S`. This supplies precisely the coproduct
presentation required by `BernsteinSplitSubrepresentationStatement`.
The presentation of `V` in that target's implication is unused. This proof
does not construct the intersections of the components of a specified
presentation, as the source's first Lemma does; it derives the requested
existence conclusion from the stronger assertion that every object splits.

The theorem `bernsteinDecompositionStatements_iff_decomposition` projects
the decomposition conjunct in the forward direction. In the reverse
direction it combines the decomposition premise, the preceding theorem and
Worker 167's published `bernsteinBlockAbelian` from
`BernsteinBlockAbelianProof`. The latter already proves exactly
`BernsteinBlockAbelianStatement`, including equality with the inherited
preadditive structure.

The construction and both theorems keep independent field and carrier universes `uF` and `uV`.
They use the original standard families, inertial classes, universe lifts,
block predicates and `Renard.IsCategoryDecomposition` through the unchanged
published statement definitions. They add no new geometric or
representation-theoretic premise to those statements. The reverse implication
in the equivalence still requires a proof of the decomposition conjunct;
it does not prove support uniqueness or construct a splitting.

The source context is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, VI.7.2, printed pp.181–184 /
PDF pp.187–190, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Worker 145 read these pages. The theorem and first Lemma are on printed
p.182 / PDF p.188; the abelian-block remark is on printed p.184 / PDF p.190.
The equivalence proved here is an internal logical consequence of the
published targets and published abelian-block proof, rather than a separate
assertion claimed to occur in the book.
