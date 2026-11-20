# Frobenius descent on affine split-special polarized framed classes

Let \(W\) be the coefficient algebra over \(\mathcal O_F\), and let \(\sigma\)
be its \(\mathcal O_F\)-algebra automorphism. The construction assumes that
the induced automorphism on \(W/\varpi W\) is the \(m\)-fold \(p\)-power
Frobenius and that the actual relative Frobenius of the fixed polarized
frame \(Y\) is an isogeny. For the residue Frobenius over the residue
field of \(F\), \(m\) is the residue degree. The tests are affine
\(W\)-algebras in which \(\varpi\) acts nilpotently.

`splitSpecialWeilFrobeniusNatIso` is the natural isomorphism of the affine
split-special functor with its composite with the test twist. It first
changes the frame from \(Y\) to \(Y^{(\sigma)}\) by the rational relative
Frobenius, then applies the coefficient comparison for the twist.
On a representative with rigidifier \(\rho\) over a test \(W\to T\), the
first step sends \(\rho\) to
\(\rho\circ(\operatorname{Frob}_{Y,T/\varpi T})^{-1}\). The second step
reads this triple on the test with structure map \(W\xrightarrow{\sigma}
W\to T\). The target and polarization are transported through the
identity on the underlying test ring. The formula in
`splitSpecialWeilFrobeniusPoint_rho` includes the source and target
identifications across the reduced coefficient square. The representative
formula descends to the isomorphism class, and the two natural
isomorphisms supply inverse and naturality laws.

`splitSpecialWeilFrobeniusPoint_hasMultiplier` takes a certificate of
multiplier \(c\) for \(\rho\) and gives a certificate of multiplier
\(p^{-m}c\) for the new rigidifier. The proof composes the torsion
pairing equation with the one for the inverse relative Frobenius and
transports it across the reduced coefficient square.

This is the Frobenius generator of Harris (A.4) on the affine
split-special functor. Representability, the component factorization
and its descent comparison, and effectivity are separate obligations.

- Michael Harris, *Supercuspidal representations in the cohomology of
  Drinfel'd upper half spaces*, Invent. Math. 129 (1997), Appendix (A.4),
  printed p. 114 (PDF p. 40), for the test twist and inverse-Frobenius
  rigidifier.
- Michael Rapoport and Thomas Zink, *Period Spaces for p-divisible
  Groups*, Annals of Mathematics Studies 141 (1996), Lemma 6.44 and its
  proof, printed pp. 309–310 (PDF pp. 321–322), for the split comparison
  and the inverse Frobenius factor \(p^{-m}\) on the dual summand.
