# Proof of the restriction quotient of the Weyl group

`Langlands.GroupScheme.relativeWeylQuotient` proves
`Langlands.GroupScheme.RelativeWeylQuotientStatement`, the quotient-group
form of Borel–Tits, *Groupes réductifs* (1965), Corollary 5.5, printed p. 97
(PDF p. 44). [Statement and source](RelativeWeylQuotientStatement.md)

Let \(D\) be the simultaneous normalizer on \(K\)-points. A point of
\(D\) in the kernel of `toT` centralizes \(T\). Precomposing its
conjugation equation with \(S_K\to T\) shows that it centralizes
\(S_K\), so the point is in the kernel of `toS`. The proof uses
`MonoidHom.liftOfSurjective` on `toT.rangeRestrict` to descend `toS`
to `toT.range`. Composing the descended map with `toT.rangeRestrict`
recovers `toS`.

The first clause of `relativeWeylAbsoluteRestriction` writes each
normalizer point of \(S_K\) as \(mz\), where \(m\) lies in \(D\) and
\(z\) centralizes \(S_K\). The Weyl classes of \(mz\) and \(m\) for
\(S_K\) coincide, so every class is hit by `toS`. The descended map
is therefore surjective.

Base change of the closed immersion supplies the monomorphism for
`fibreRelativeWeylGroupEquiv`, which identifies the Weyl quotient of
\(S_K\) with the point Weyl quotient for \(S\) evaluated on
\(\operatorname{Spec} K\). Since this test scheme is connected,
`relativeWeylGroupRestrict_bijective` makes restriction from the
Weyl group over \(k\) a multiplicative equivalence to the same point
quotient. Composing the descended map with the fibre equivalence
and then with the inverse of restriction gives the required surjection.
On composing again with restriction, the inverse cancels, and the descent
equation gives the stated equality of homomorphisms on \(D\).
