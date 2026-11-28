# The compact conjugation pushforward in a semisimple descent

Let \(A\) be a finite-dimensional complete ultrametric normed algebra
over a proper nontrivially normed field. Embed its unit group openly
in a Hausdorff topological group \(H\) by \(i\). Suppose \(s\in H\)
induces an algebra automorphism \(\alpha\) by conjugation on that unit
group. Write \(S=A^\alpha\) and \(U=\operatorname{adjointConjugationDomain}(\alpha)\).
Let \(K\) be an open unit subgroup and \(M\subset S^\times\) the norm
congruence subgroup of radius \(0<r<1\), with the closed ball of radius
\(r\) in \(S\) contained in \(U\). The algebra and its unit group are
second countable. The measures on \(H,A^\times,S,S^\times\) use their
Borel structures.

`compactSemisimpleDescentPushforward` applies to a test pushforward for
\((g,Y)\mapsto g(1+Y)\alpha(g)^{-1}\). The source measures are the pullback
of bi-invariant Haar \(\nu\) along \(g\mapsto i(g)s\) and the restriction
of additive Haar \(\rho\) to \(U\). If evaluation against a distribution
on \(H\) in the coset coordinates satisfies the descent tensor identity
with slice distribution \(T\), the theorem gives a test pushforward for
\((k,m)\mapsto k(s i(m))k^{-1}\) on \(i(K)\times M\). Here \(i(m)\)
means the inclusion through the units of \(S\). The source measures are
\(\nu\) pulled back to \(i(K)\) and \(\rho\) pulled back by \(m\mapsto m-1\).
On a tensor test the ambient distribution of the pushforward equals
the conjugator integral times \(T\) of the slice test extended along
\(m\mapsto m-1\) into \(U\).

The conjugator chart inverts the open subgroup image equivalence. The
coset pullback of \(\nu\) equals its pullback along \(i\) by right
invariance. Since \(m\) belongs to the fixed algebra, its image commutes
with \(s\). Substitution into the normalized conjugation map identifies
it with compact conjugation after the target embedding. Applying
`restrictedDescentPushforward` gives both identities. For compact \(K\),
this is the pushforward used on compact conjugators in Clozel's Lemma 5.
[Clozel 1987, §3.4, printed p. 154](https://doi.org/10.4153/CJM-1987-008-3)
