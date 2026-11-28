# Haar density for radical-first multiplication

Let \(i\colon N\to H\) be a group homomorphism and a topological embedding
onto the kernel of a continuous group homomorphism \(p\colon H\to M\).
Let \(j\colon M\to H\) be a continuous group homomorphism with \(p\circ j\)
the identity. The existing `prodHomeomorph` uses \(i(n)j(m)\). Inversion on each group gives the
homeomorphism `complementFirstHomeomorph` with value \(j(m)i(n)\).

For the measure identities, give \(N\), \(M\) and \(H\) their Borel measurable
structures and assume \(N\) is second countable. The left Haar measures \(dn\)
and \(dm\) are s-finite, meaning each is a countable sum of finite measures.
`isHaarMeasure_map_complementFirst` pushes their product through \(j(m)i(n)\).
Under left multiplication by \(g\), the first
coordinate is translated by \(p(g)\). For each first coordinate \(m\), the
second coordinate is translated by the normal component of \(g j(m)\)
in complement-first order. The product measure is invariant by this
skew-product transformation. Positivity on open sets and finiteness on
compact sets transport by the homeomorphism.

For the density calculation assume \(N\) is locally compact.
Write \(\alpha_m\) for conjugation by \(j(m)\) on \(N\) and \(\delta(m)\)
for `mulEquivHaarChar` of this automorphism. The two maps are related by
\(j(m)i(n)=i(\alpha_m(n))j(m)\). The pushforward of \(dn\) under \(\alpha_m\)
is \(\delta(m)^{-1}dn\). For a measurable subset of \(H\), the proof applies
that identity to each normal-coordinate fiber, then uses the product
measure and density formulas. It obtains `map_complementFirst_eq_map_weightedProduct`
and hence `isHaarMeasure_map_weightedProduct` with measure
\(dn\,\delta(m)^{-1}dm\). This calculation gives the inverse density used
in the adelic formula (7.7).

The adelic use is in P. Delorme, *On the spectral theorem of Langlands*,
Advances in Mathematics 426 (2023), 109107, p. 24, equation (7.7).
