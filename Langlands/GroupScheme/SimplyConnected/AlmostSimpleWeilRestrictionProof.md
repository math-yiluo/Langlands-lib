# Simply connected almost-simple groups are actual Weil restrictions

Author: Worker 166.

`Langlands.GroupScheme.simplyConnectedAlmostSimpleWeilRestriction.{u}` proves
exactly the published
`Langlands.GroupScheme.SimplyConnectedAlmostSimpleWeilRestrictionStatement.{u}`.
The universe `u`, ground field, and characteristic are arbitrary. The proof
retains the original `IsSimplyConnected`, `IsAlmostSimple`,
`IsAbsolutelyAlmostSimple`, and `AffineWeil.groupScheme` definitions. There is
no extra perfectness, infinitude, topological or local-field premise.

The implemented proof follows the geometric-factor descent route described in
the published target's Markdown, rather than treating the resulting
isomorphism as an assumption. The external structural context remains
Borel–Tits, *Groupes réductifs* (1965), registered
`borel-tits-1965-groupes-reductifs`, 6.17–6.21(ii), printed pp.111–113 /
PDF pp.58–60, and Milne, *Algebraic Groups* (2017), registered
`milne-2017-algebraic-groups`, Theorem 24.3, printed pp.512–513 /
PDF pp.528–529. Their mathematical inputs are used through the previously
published Library proofs. This module supplies the actual comparison and
assembly; it adds no further external assumption.

First, `SimplyConnectedAlmostSimpleProduct.exists_weilRestriction_of_isSepClosed`
works with a supplied product decomposition `D` of `G_L` over a separably closed
Galois extension. For a selected original factor index `i`, the published
stabilizer construction supplies the finite separable field
`D.factorStabilizerField i` and actual descended group
`(D.factorStabilizerDescent i).1`, with its affine and locally finite type
properties. The existing descent-properties results give simple connectedness
and, over the separably closed upper field, absolute almost-simplicity of this
group.

Every minimal polynomial from the finite separable stabilizer field splits in
`L`, by separability and `IsSepClosed.splits_codomain`. The proved canonical
tensor decomposition therefore supplies the original actual Weil-product
isomorphism `AffineWeil.embeddingProductIsoOfBijective`.
`AffineWeil.embeddingProductIsoOfBijective_descent`, proved in the accompanying
`AffineWeilEmbeddingGalois` module, supplies its compatibility with the canonical
Galois transport on the original embedding coordinates. The published
`exists_weilRestriction_of_compatibleEmbeddingProduct` then composes it with
the original conjugate-factor product isomorphism and descends the actual
isomorphism by `Descent.GaloisHom.iso`. It returns all required field, group,
property and isomorphism witnesses.

Finally, the closed theorem takes `L = SeparableClosure k`. Published
`isSimplyConnectedFieldExtension` gives simple connectedness of `G_L`, and the
proved `almostSimpleProduct` construction supplies `D`. Almost-simplicity of
the original group makes its index type nonempty, via
`D.nonempty_index_of_almostSimple`. The preceding witness lemma applies to any
selected index. Smoothness and the affine morphism supply the quasi-compact,
quasi-separated and locally finite presentation instances required by actual
Galois descent. All of these are consequences of the stated hypotheses.

The result is the required `Nonempty (G ≅ AffineWeil.groupScheme k E H)` for an
absolutely almost-simple simply connected `H` over a finite separable `E/k`.
No uniqueness is asserted. The proof does not use `LocalKneserTitsStatement` or
its planned consumers. The published target pair and its import closure are
unchanged.
