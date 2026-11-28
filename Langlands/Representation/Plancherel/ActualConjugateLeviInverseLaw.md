# Inverse of an actual translated comparison

`ActualConjugateLeviCoherence.inverseLaw` proves both inverse equations
for certified comparisons at \(g\) and \(g^{-1}\), through the canonical
return map `ActualConjugateLeviFiberTransport.inverseEquiv`.

The return map has constant value in the fixed compact charts, by
`inverseTransport_chartValue_const`, and preserves the coefficients, by
`anchorChange_coefficientMap`. Each certified comparison preserves the
coefficients and is locally finite in its own compact charts. The inverse
comparison is reindexed along `unitaryConjugateParameter χ g`, so the two
comparisons and the return map form a weakly continuous loop on the original
fiber. The loop and the identity preserve the same coefficients.
`eq_of_chain` uses dense source coefficient injectivity to show that the
loop is the identity at every unitary parameter.

This gives the left inverse equation. Surjectivity of the forward comparison
gives the right inverse equation. The two equations are expressed by
`TransportedInverse` with the actual return map.

The inverse equation belongs to the coherence of the comparisons in
Waldspurger, *La formule de Plancherel pour les groupes p-adiques*
(2003), V.3 formula (1) and Lemma V.3.2, printed p. 295, PDF p. 61.
[Original publication](https://doi.org/10.1017/S1474748003000082)
