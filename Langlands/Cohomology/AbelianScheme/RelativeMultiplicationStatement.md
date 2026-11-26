# Multiplication on relative étale cohomology of an abelian scheme

Let \(\pi:A\to S\) be an abelian scheme and let \(p\) be a prime invertible
on \(S\). On the small étale site of \(S\), the pullback induced by the
integer multiplication morphism \([m]:A\to A\) acts on
\(R^q\pi_*\underline{\mathbb Z/p^r\mathbb Z}\) as multiplication by
\(m^q\).

`Langlands.Cohomology.AbelianRelativeEtale.RelativeAbelianMultiplicationCohomologyStatement`
asserts equality of these endomorphisms of the actual higher direct
image for \(q,r\ge 0\) and \(m\in\mathbb Z\). The multiplication
morphism comes from `Langlands.AbelianScheme.multiplication`.
`relativeConstantDerivedPullback` constructs pullback for an \(S\)-map
between two schemes over \(S\). It applies the derived adjunction unit,
compares the composite direct image by the adjunctions for the exact
inverse images, and uses the canonical inverse image isomorphism for
constant coefficients. `relativeConstantCohomologyPullback` takes
homology and uses the comparison with the higher derived functors.

Proper base change reduces the equality to geometric fibres. Over an
algebraically closed field, the dual Tate module identification makes
\([m]^*\) act by \(m\) in degree one. The exterior power description by
cup products makes it act by \(m^q\) in degree \(q\). The same calculation
gives freeness in all degrees. Proper finiteness and the exact adic
reduction sequence identify finite-coefficient cohomology of the fibre
with reduction of the integral calculation, since the next integral
cohomology group has no \(p^r\)-torsion. This gives the equality for the
finite prime-power coefficient sheaf.

- J. S. Milne, *Abelian Varieties*, author revision of 2 January 2022,
  §15, Theorem 15.1(a)–(b), p. 27 (PDF p. 27), and its proof, pp. 27–28.
  Registered ID `milne-abelian-varieties-1986-author-2022`, SHA-256
  `bffdf81c57c77420b5454b31270007989d12f332abea62424be15c424079fc7c`.
- J. S. Milne, *Étale Cohomology* (1980), V.1, Lemma 1.11, pp. 165–166,
  for the adic reduction sequence. Registered ID
  `milne-1980-etale-cohomology`, SHA-256
  `0a2f02682f82db8385e4dc6c77c7113900b11d6c313f34f8b354a3a9a391d232`.
- *SGA 4*, tome 3, Exposé XII, Corollary 5.2(iii), printed p. 89
  (PDF p. 92), for proper base change, and Exposé XIV, Corollary 1.2,
  printed p. 145 (PDF p. 148), for proper finiteness. Registered ID
  `sga4-1973-tome3-deligne-xvii-original-scan`, SHA-256
  `702fa23766ccec841d31ce0f21dfaacff8d8d31d4153de386587a27a4c01107a`.
- Harris–Taylor, *The Geometry and Cohomology of Some Simple Shimura
  Varieties* (2001), III.2, printed p. 98 (PDF p. 106), applies the
  corresponding degree weights for \([2]\) to the actual relative
  powers of the tautological family with rational adic coefficients.
  Registered ID `harris-taylor-2001-geometry-cohomology-simple-shimura`,
  SHA-256
  `5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.
