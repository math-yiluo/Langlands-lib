# Split Bruhat decomposition on rational points

`Langlands.GroupScheme.SplitBruhatRationalPointsStatement` applies to a
connected reductive group \(G\) over any field \(k\) and a Borel pair
\((B,T)\) whose maximal torus \(T\) is split. The predicate
`BorelTorusBruhatRationalPoints b t` asserts that the Weyl group of \(T\)
indexes \(B(k)\backslash G(k)/B(k)\) by the bijection \([n]\mapsto B(k)nB(k)\).
The formula on every representative specifies the bijection. In
particular the double cosets cover \(G(k)\), and distinct Weyl elements give
disjoint cosets.

`normalizerPoints t` uses rational points whose conjugation restricts to
an actual automorphism of \(T\). The quotient `relativeWeylGroup t`
has denominator the rational points of the centralizer of \(T\). For this
maximal torus those points are \(T(k)\) by `maximalTorusCentralizer`.
The two subgroups on the double-coset side are both the image of
the actual \(B(k)\) in \(G(k)\).

## Sources

J. S. Milne, *Algebraic Groups* (2017), Proposition 21.1, printed p. 424
(PDF p. 440), identifies the Weyl group with \(N_G(T)(k)/T(k)\). The opening
formula of §21.h, printed p. 446 (PDF p. 462), is the disjoint rational
point decomposition used here. Remark 21.74, printed p. 447 (PDF p. 463),
identifies the pieces with the Borel double cosets. Registered source
`milne-2017-algebraic-groups`, SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.

The geometric double-coset decomposition is also in Borel and Tits,
*Groupes réductifs* (1965), §§2.3–2.4, printed pp. 64–65 (PDF pp. 11–12).
Registered source `borel-tits-1965-groupes-reductifs`, SHA-256
`ec6674ba292deaadd77a449f4bad3750db79c0b87b117a892ef6b09bb16357ad`.
