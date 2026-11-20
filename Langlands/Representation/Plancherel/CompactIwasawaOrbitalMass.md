# An orbital test for the compact Iwasawa normalization

For a point \(a\) centralizing the common Levi and lying in the compact open
subgroup \(K\), `compactConjugationIndicator` is the function
\(g\mapsto\mathbf1_K(g^{-1}ag)\). It is invariant under left translation by
the Levi. For \(g=uk\) with \(k\in K\), its value is the indicator of the
condition \(a^{-1}u^{-1}au\in K\). With radical Haar mass one on \(K\cap U\),
the integral in \(u\) is the pushforward scale of that displacement map.

`iwasawaExchangeRatio_eq_one_of_compactConjugation` computes both
Iwasawa pushforwards on this test. The outer factor is the common Haar mass
of \(K\). If the two radical masses agree and are positive and finite, the
known proportionality of the pushforwards forces the ratio to be one.
The result is an internal normalization argument for the compact probability
pairings in Waldspurger's IV.1(11) and Lemma V.3.1.
