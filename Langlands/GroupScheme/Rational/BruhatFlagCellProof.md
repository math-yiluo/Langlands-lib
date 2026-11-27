# Proof of the rational Bruhat cells in the flag quotient

`Langlands.GroupScheme.rationalBruhatFlagCell` proves
[`RationalBruhatFlagCellStatement`](BruhatFlagCellStatement.md) over an
arbitrary field \(k\). Write \(P=P_G(\chi)\), \(U=U_G(\chi)\),
\(V=U_G(\chi^{-1})\), and \(W_n=nVn^{-1}\cap U\). The proof uses the
supplied \(q\colon G\to Q\) throughout. Affine representability identifies
the range of the chosen inclusion of \(P\) with the dynamic parabolic, so
the exact fibre relation applies to that inclusion on every test scheme.

## The immersion

The projection \(W_n\to V\) is a closed immersion by base change of the
closed inclusion \(U\to G\). By `oppositeCellStatement`, multiplication
\(V\times_k P\to G\) is an open immersion. The exact fibre relation
identifies that multiplication as the pullback of \(V\to Q\) along \(q\).
Smoothness gives flatness, so surjectivity and quasi-compactness make \(q\)
an fpqc cover and `QuotientCell.isOpenImmersion` gives the open chart
\(V\to Q\). The descended left translation by \(n\) is an isomorphism of
\(Q\). Its compatibility with \(q\) expresses the flag map as the composite
of the closed projection, the open chart, and this isomorphism.

## Rational images and Weyl classes

`BruhatFlagCell.lift_groupParametrization_comp` uses the group cell
multiplication formula to identify \(q(anb)\) with the flag image of \(a\)
on every test scheme, for \(a\) in \(W_n\) and \(b\) in \(P\). Right
multiplication by \(b\) preserves \(q\) by the exact fibre relation. Taking
\(b=1\) shows that every flag image comes from the group cell, and projecting
any point of \(W_n\times_k P\) to \(W_n\) gives the same quotient image.
Since `rationalBruhatCell` identifies the group-cell image on \(k\)-points
with \(P(k)nP(k)\), the flag-cell image is exactly
\(\{q(pn)\mid p\in P(k)\}\).

Two normalizer points of the same relative Weyl class differ on the right
by a point of \(C_G(T)(k)\subseteq P(k)\). The fibre relation then identifies
their flag-cell images, so `Quotient.lift` defines the family of sets indexed
by the relative Weyl group.

Over a finite field, the proof lifts \(x\in Q(k)\) using
`rational_lifts_of_finite_torsor` and `finiteFieldTorsorPointStatement`.
The fibres are torsors under the smooth connected affine group \(P\).
Over an infinite field, `rational_lifts_of_reductive_density` uses
`reductiveRationalPointDensity` and the opposite flag chart with its section
near the identity coset. The natural equivalence `rationalPointEquiv`
transfers both lifting results to morphisms in the category of schemes
over \(\operatorname{Spec}k\).

The covering assertion of `rationalBruhat` writes a lift as \(a n b\) with
\(a,b\in P(k)\), so \(x=q(an)\) belongs to the cell of \(n\). For uniqueness,
if \(q(an)=q(bn')\), the fibre relation gives
\(d=(an)^{-1}(bn')\in P(k)\). Then \(n'=b^{-1}a\,n\,d\), so the
separation assertion of `rationalBruhat` identifies the relative Weyl
classes of \(n\) and \(n'\).
