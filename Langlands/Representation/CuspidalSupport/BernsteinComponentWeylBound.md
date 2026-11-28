# A uniform bound on the orders of Bernstein component groups

Fix a connected reductive group \(H\) over a nonarchimedean local field \(F\)
and an embedding \(j:H\to G\) given by a monomorphism on the underlying
schemes over \(F\). Suppose \(n\) rational points of \(G\) cover the
rational normalizer of \(j\) modulo right multiplication by \(H(F)\).
`RationalWeylGroupCardBoundStatement` bounds the order of the group
`ComponentWeyl.weylGroup j ρ` for every smooth irreducible complex
representation \(\rho\) of \(H(F)\). The bound is \(n|C|\), where \(C\)
is the fixed group of unramified characters of \(H(F)\) trivial on its
point-group centre.

`mem_centralTrivial_of_twist_iso` compares the central action on \(\rho\)
with that on an isomorphic twist. The actual central character acts by
a nonzero scalar at each central element. Evaluating the intertwining
identity on a nonzero vector and cancelling that scalar gives
\(\chi(z)=1\) for each central \(z\). The finite-index theorem for the
common norm kernel joined with the centre gives finiteness of \(C\)
through `finite_centralTrivialUnramifiedCharacters`.

For each normalizer coset that contributes permutations, the proof
chooses a self-conjugacy \(c_0\) and one character \(\chi_0\) that
realizes \(\rho^{c_0}\) as a twist. Self-conjugacies whose points differ by
right multiplication by \(H(F)\) induce the same twist sets and affine
permutations. Thus every contributing character \(\chi\) in this coset
satisfies \(\rho\otimes(\chi\chi_0^{-1})\simeq\rho\), and its permutation
is determined by the coset and the element \(\chi\chi_0^{-1}\) of \(C\).
Choosing one such label for each permutation embeds the component group
in `Fin n × C`. `rationalWeylGroup_card_le` obtains both finiteness and
the stated cardinal bound from this embedding.

This bound quantifies the finite-group quotient description of
Bernstein components in Renard, *Représentations des groupes réductifs
p-adiques* (9 July 2026), VI.7.1, printed p. 181 (PDF p. 187). It
provides a uniform input for the finiteness calculation of VI.10.5,
printed p. 213 (PDF p. 219).
