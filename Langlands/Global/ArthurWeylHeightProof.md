# The uniform Weyl displacement bound for the minimal Iwasawa height

`Langlands.Global.ArthurTruncation.weylHeightLowerBound` proves
`WeylHeightLowerBoundStatement`. For the Iwasawa height \(H_0\) of the specified compact subgroup
\(K\), a full fundamental weight \(\varpi=\varpi_\beta\), and the adelic image \(w\) of a rational
normalizing point with Weyl class \(s\), the theorem produces \(B\geq 0\) such that
\[
  \varpi(H_0(x)) \leq (s\varpi)(H_0(wvx)) + B
\]
for all \(v\in N_0(\mathbb A_F)\) and \(x\in G(\mathbb A_F)\). The subgroup \(K\) is compact and
satisfies \(P_0(\mathbb A_F)K=G(\mathbb A_F)\).

## The parabolic line and its Weyl translate

`exists_maximalParabolic_dominant_line` supplies a Chevalley representation with a coordinate
line stabilized by the standard maximal parabolic omitting \(\beta\). Write \(\chi_1\) for its
line character on \(P_0\). Conjugating the generic cocharacter by \(w^{-1}\) keeps it in the
maximal split torus, which preserves the original line. A rational basis change diagonalizes
this conjugate cocharacter and keeps the original vector as a basis vector \(e_a\). Write
\(\sigma\) for the representation in that basis and
\(\tau(g)=\sigma(w^{-1}gw)\). The original generic cocharacter is diagonal in \(\tau\).
The rational vectors \(v_2=e_a\) and \(v_1=\tau(w^{-1})v_2\) are nonzero. The first line in
\(\tau\), spanned by \(v_1\), has character \(\chi_1\) on \(P_0\). The unipotence of \(N_0\)
makes \(\chi_1\) trivial there, so for \(y=wvx\) the two inverse-orbit vectors agree,
\(\tau(x^{-1})v_1=\tau(y^{-1})v_2\).

The dynamic limit of a point \(q\) of \(P_0\) gives its factor in the minimal Levi \(M_0\),
which is the centralizer of the maximal split torus. Conjugation by the inverse lift preserves
that centralizer. Composing the limit with this conjugation, followed by inclusion in
\(P_0\), gives a morphism \(P_0\to P_0\). Pulling back \(\chi_1\) along it yields \(\chi_2\).
The limit restricts to the identity on the embedded split torus, so the restriction of
\(\chi_2\) is the inverse pullback of the restriction of \(\chi_1\) by the torus automorphism
of the lift. This is the Weyl action used in the statement.

In \(\tau\) the image of the Levi limit is the block-diagonal part of the matrix of \(q\),
with blocks of equal cocharacter degree. `GeneralLinear.hasLimit_diagonalCocharacter_iff`
gives this equality on the actual adele coefficient scheme. In particular the diagonal entry
at \(a\) is retained. On the Levi limit the \(a\)-th coordinate of the action on \(e_a\) is
\(\chi_2(q)\), by the line action of \(\sigma\) on the inverse conjugate of the limit. Thus
\((\tau(q)v_2)_a=\chi_2(q)\).

## The height comparison

In the Iwasawa coordinates of \(x\), the inverse parabolic factor scales \(v_1\) by the
inverse of \(\chi_1\). In the Iwasawa coordinates of \(y\), the inverse parabolic factor
acting on \(v_2\) has an invertible coordinate equal to the inverse of \(\chi_2\). Its idele
norm is bounded by the primitive-vector height, since the absolute value of that coordinate
is bounded by the maximum at every place. The finite products have finite multiplicative
support and use the same archimedean multiplicities.

The compact matrix image of \(K\) gives a two-sided distortion bound for primitive-vector
heights. Apply it to the inverse compact factors of \(x\) and \(y\), using that their
inverse-orbit vectors agree. If \(L_1\) and \(L_2\) are the logarithmic Iwasawa evaluations
of \(\chi_1\) at \(x\) and \(\chi_2\) at \(y\), this yields
\(\exp(-L_2)\leq M\exp(-L_1)\) for a positive constant \(M\) from the compact distortion
bound and the height of \(v_1\). Taking logarithms gives \(L_1\leq L_2+C\) with
\(C=\max(\log M,0)\).

The simple reflection for \(\beta\) gives a positive coroot pairing \(d\) of the line
character, and the reflections for the other simple roots fix it. Thus the restriction
of \(\chi_1\), viewed as a real character, differs from \(d\varpi\) by an element of the
annihilator of the simple coroots. `standardLeviRealDecomposition` identifies that
annihilator with restrictions of real combinations of rational characters of \(G\).
Those restrictions are Weyl invariant. Their values on the Iwasawa height equal the
ambient character logarithms, since the logarithms vanish on the compact factor.
The ambient logarithms of \(y\) and \(x\) agree by the product formula for \(w\) and
unipotence of \(v\). Cancelling these terms and dividing by \(d>0\) yields \(B=C/d\).

## Source

The estimate is the derived uniform version of the Weyl-transported height inequality
used in J. Arthur, *A trace formula for reductive groups II* (1980), proof of Lemma 1.1,
printed p. 91 (PDF p. 6). Literature ID `arthur-1980-trace-formula-reductive-groups-II`,
SHA256 `12f250ae40730909b8cc1e9c0d679840fd0e57676f2772800f8688c125b6440f`.
[Original article](https://www.numdam.org/item/CM_1980__40_1_87_0/)
