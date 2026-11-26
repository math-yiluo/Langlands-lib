# The unipotent scheme product for a rational Bruhat cell

`Langlands.GroupScheme.RationalBruhatFactorizationStatement` concerns a
connected reductive group \(G\) over any field \(k\), a maximal \(k\)-split
torus in \(G\), and a generic cocharacter \(\chi\) of that torus. Write
\(U=U(\chi)\) and \(V=U(\chi^{-1})\). For each rational point \(n\) of the
torus normalizer, the proposition asserts that multiplication is an
isomorphism of \(k\)-schemes
\[
(U\cap n V n^{-1})\times_k(U\cap n U n^{-1}) \longrightarrow U.
\]

The factors are scheme-theoretic intersections. Their inclusions use the
affine representatives of the dynamic unipotent functors for \(\chi\),
\(n\chi^{-1}n^{-1}\), and \(n\chi n^{-1}\). Conjugation of cocharacters
transports their unipotent functors by `Dynamic.mem_unipotent_conj`.
`BruhatFactorization.multiplication` projects each intersection to the
common subgroup and multiplies there. The asserted isomorphism thus
parametrizes every test-scheme point of \(U\), including those over
nonreduced schemes.

This is the product of unipotent factors in Borel–Tits, *Groupes réductifs*
(1965), §5.13(1), p. 99, with the ordering used in the proof of §5.15, p. 100.
Milne, *Algebraic Groups* (2017), §25.27, p. 551, also gives the variety
product for the two unipotent factors. The author’s Chapter 25 errata entry
for p. 545 et seq. specifies that the parabolic in §25.27 is minimal and
that the split torus is maximal in it. `rationalBruhat_parabolic_isMinimal`
identifies the parabolic of the generic cocharacter as minimal. The
statement expresses the variety product using the corresponding subgroup
schemes and their actual multiplication.
