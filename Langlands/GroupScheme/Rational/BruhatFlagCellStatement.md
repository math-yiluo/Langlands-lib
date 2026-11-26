# Rational Bruhat cells in the flag quotient

`Langlands.GroupScheme.RationalBruhatFlagCellStatement` takes a connected
reductive group \(G\) over an arbitrary field \(k\), a maximal split torus
\(T\subseteq G\), and a generic cocharacter \(\chi\) of \(T\). Let
\(P=P_G(\chi)\), \(U=U_G(\chi)\), and \(V=U_G(\chi^{-1})\). The input
\(q:G\to Q\) is a smooth, surjective, quasi-compact morphism of
\(k\)-schemes with the exact right-\(P\)-coset fibre relation on every
test scheme.

For each \(n\in N_G(T)(k)\), the morphism `BruhatFlagCell.parametrization`
from \(W_n=nVn^{-1}\cap U\) to \(Q\) is a locally closed immersion. The
intersection is a scheme pullback. The map projects to \(V\), translates
on the left by \(n\), then applies \(q\). Under the inclusion of \(W_n\)
in \(G\), this sends \(a\) to \(q(an)\).

Its image on rational points is the set of \(q(pn)\) for \(p\in P(k)\).
The rational-point images descend to the relative Weyl quotient
\(N_G(T)(k)/C_G(T)(k)\), and each point of \(Q(k)\) belongs to exactly
one such image.

## Source and scope

Milne, *Algebraic Groups* (2017), §25.27, printed p. 551 (PDF p. 567),
gives the cell parametrization in the parabolic quotient. The author
errata entry “p.545 et seq.” requires a minimal parabolic and a maximal
split torus of that parabolic. The generic cocharacter supplies these
conditions by `rationalBruhat_parabolic_isMinimal`. Milne, Theorem 25.9(b),
printed p. 546 (PDF p. 562), supplies the ground-field point comparison
for the projection. Borel–Tits, *Groupes réductifs* (1965), Theorem 5.15,
printed pp. 100–101 (PDF pp. 47–48), gives the ground-field double-coset
partition used for the indexing. The immersion assertion concerns schemes
over \(k\), and the partition concerns \(Q(k)\) with this ground-field
relative Weyl group.
