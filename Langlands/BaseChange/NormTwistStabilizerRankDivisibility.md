# Rank divisibility of the norm-twist stabilizer

Let \(F\) be a characteristic-zero nonarchimedean local field and \(E/F\) a cyclic
field extension of degree \(\ell\) with generator \(\sigma\). For an irreducible
admissible complex representation \(\pi\) of \(\mathrm{GL}_n(F)\),
`NormTwistStabilizerRankDivisibilityStatement` says that the order of
`normTwistStabilizer E π` divides \(\gcd(\ell,n)\). The fields and the
representation carrier have independent universes.

The extension-degree divisibility is `normTwistStabilizer_card_dvd`. For the rank
divisibility, `admissibleSchur_centralCharacter` gives the scalar by which \(aI_n\)
acts. An equivalence of \(\pi\) with its twist by \(\kappa\circ\det\) then gives
\(\kappa(a)^n=1\) by cancellation on a nonzero vector. The Galois group of the
universe-zero field models is cyclic. Its abelianization projection, the finite
norm abelianization equivalence and norm-subgroup transport give a surjection
onto \(F^\times/N_{E/F}(E^\times)\), so the actual norm quotient is cyclic.

Choose a representative of a generator of the actual norm quotient. A character
trivial on norms is determined by its value on this representative. For \(n>0\),
evaluation therefore embeds the stabilizer in the group of complex \(n\)-th roots
of unity. This group has order \(n\), so Lagrange's theorem gives rank divisibility.
For \(n=0\) the rank divisibility follows from divisibility of zero.

Henniart–Lemaire, *Changement de base et induction automorphe pour GL_n en
caractéristique non nulle*, II.1.3, printed p. 56, defines the norm-character
group. Their II.4.12, printed p. 96, gives rank divisibility in the
supercuspidal lift setting. The scalar and character argument above derives it
for any irreducible admissible representation of the base group.
