# Locally closed multiplication for a rational Bruhat double coset

`Langlands.GroupScheme.RationalBruhatCellStatement` concerns a connected
reductive group \(G\) over any field \(k\), a maximal split torus \(T\)
in \(G\), and a generic cocharacter \(\chi\) through \(T\). The supplied
maps represent \(P=P_G(\chi)\), \(U=U_G(\chi)\), and \(V=U_G(-\chi)\).
Representability here includes equality of ranges on every test scheme.
The hypothesis that \(U\to G\) is closed gives a closed intersection
inside the conjugate of \(V\).

For a rational point \(n\) normalizing the actual torus \(T\),
`BruhatCell.factor u v n` is the scheme-theoretic intersection
\(W=nVn^{-1}\cap U\). The map `BruhatCell.parametrization u v p n`
sends \((a,p')\) to \(a n p'\). Its definition first projects the
intersection to \(V\) using \(a\mapsto n^{-1}a n\), then applies
opposite-cell multiplication and left translation by \(n\).
The proposition asserts that this map from \(W\times_k P\) is a
locally closed immersion in \(G\) with rational-point image
exactly \(P(k)nP(k)\).

## Source and scope

J. S. Milne, *Algebraic Groups* (2017), §25.27, printed p. 551
(PDF p. 567), gives the product parametrization by \(U^w\times P\).
The registered book source is
`milne-2017-algebraic-groups`, SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.

The author errata entry “p.545 et seq.” requires a minimal parabolic
and a maximal split torus of it. The generic cocharacter of the
maximal split torus gives those data by `rationalBruhat_parabolic_isMinimal`.
Registered errata source `milne-2017-algebraic-groups-errata-2026-11-02`,
SHA-256 `a0c3a10dc376e1c9bd1de05b33beaf7d54e5f1ea7b408d594cfd70231a7ba0cf`.

Borel and Tits, *Groupes réductifs* (1965), Theorem 5.15, printed
pp. 100–101 (PDF pp. 47–48), use the intersection with the conjugate
of \(U^-\) and the restriction of the opposite cell to parametrize
the unipotent double coset. Passing to \(P=U C_G(T)\) gives the
displayed parabolic double coset. Registered source
`borel-tits-1965-groupes-reductifs`, SHA-256
`ec6674ba292deaadd77a449f4bad3750db79c0b87b117a892ef6b09bb16357ad`.

The immersion is a scheme statement. The image comparison is over
the ground field. The product decomposition of \(U\) by the two
intersections and the cell decomposition of \(G/P\) are separate
assertions in the sources.
