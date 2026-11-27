# Affine spaces for the unipotent factors of rational Bruhat cells

`Langlands.GroupScheme.RationalBruhatCellAffineSpaceStatement` concerns a
connected reductive group \(G\) over any field \(k\) and a maximal \(k\)-split
torus \(i:T\hookrightarrow G\). Let \(\nu\) be generic for the relative roots,
and write \(\chi=i\circ\nu\). Use the closed affine representatives
\(U=U(\chi)\) and \(V=U(-\chi)\) of the identity-limit functors. For each
rational normalizer point \(n\in N_G(T)(k)\), the actual group scheme
\[
W_n = nVn^{-1}\times_G U
\]
is `BruhatCell.factor` for these representatives. The fibre product represents
the intersection on every test scheme.

The proposition gives a natural number \(d\) such that \(W_n\) has a split
series of length \(d\), is smooth of relative dimension \(d\) over \(k\), and
admits an isomorphism \(W_n\simeq\mathbb A^d_k\) in `Over (Spec k)`.
`RelativeRoot.HasSplitSeries` expresses the series by actual closed
subgroups and fppf quotients with one-dimensional vector group quotients.
The affine-space conclusion is an existence assertion about the underlying
schemes.

## Source and derivation

Borel–Tits, *Groupes réductifs* (1965), §§5.12–5.13, printed p. 99
(PDF p. 46), identify the negative-root factor for a Weyl representative
with \(U\cap nVn^{-1}\), using the positive and negative systems of the
chosen order. Theorem 5.15, printed pp. 100–101 (PDF pp. 47–48), uses this
factor in the rational Bruhat product. The sign of the pairing with the
generic cocharacter gives the positive and negative relative roots.

For a rational normalizer point, conjugating the inverse cocharacter
gives another cocharacter of \(T\). Its conjugation action preserves
\(U\), and its identity-limit subgroup inside \(U\) is the displayed
intersection. The smooth affine group with this action has a smooth split
unipotent identity-limit subgroup. This is the contracting-subgroup
specialization of the split-torus action results of Milne, *Algebraic
Groups* (2017), Proposition 16.63, printed p. 347 (PDF p. 363).
Milne, Definition 14.61 and §14.66, printed p. 299 (PDF p. 315), give
the split-series and affine-space descriptions. Each step of a split
series adds one to the relative dimension.
