# An orbital test for the compact Iwasawa normalization

For a point \(a\) centralizing the common Levi and lying in the compact open
subgroup \(K\), `compactConjugationIndicator` is the function
\(g\mapsto\mathbf1_K(g^{-1}ag)\). It is invariant under left translation by
the Levi. Let \(L_U(u)=a^{-1}u^{-1}au\) be the displacement on \(U\)
when conjugation by \(a^{-1}\) gives an automorphism of \(U\). For \(g=uk\)
with \(k\in K\), the value is the indicator of \(L_U(u)\in K\cap U\).
Its integral in \(u\) is the preimage mass \(\mu_U(L_U^{-1}(K\cap U))\).
`measure_compactConjugationPreimage_of_map` identifies this mass with \(c\)
under the supplied identity \((L_U)_*\mu_U=c\mu_U\) and the normalization
\(\mu_U(K\cap U)=1\).

`iwasawaExchangeRatio_eq_one_of_compactConjugation` computes both
Iwasawa pushforwards on this test. The outer factor is the common ambient
Haar mass of \(K\). If the two radical displacement preimage masses agree
and their common value is positive and finite, the known proportionality
of the pushforwards forces the ratio to be one.
The result is an internal normalization argument for the compact probability
pairings in Waldspurger's IV.1(11) and Lemma V.3.1.
