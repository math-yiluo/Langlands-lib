# Composition of actual translated comparisons

`ActualConjugateLeviCoherence.compositionLaw` proves that the certified
comparison at \(t\), followed by the one at \(s\) at the conjugated parameter,
agrees with the certified comparison at \(st\) after the canonical
identification of the two target fibers.

The comparison for \(s\) is reindexed along `unitaryConjugateParameter χ t`.
Local finiteness of the two certified families and constancy of
`ActualConjugateLeviFiberTransport.multiplicationEquiv` in the fixed compact
charts make the composite weakly continuous. Each comparison in the composite
preserves the coefficients by its certificate, and the last transport
preserves them by `anchorChange_coefficientMap`. The comparison at \(st\)
also preserves coefficients and is pointwise bijective and weakly continuous.
`eq_of_chain` proves agreement at every unitary parameter from dense source
coefficient injectivity. `transportedComposite_iff` gives the pointwise
transported equality of `Composes`.

The order of multiplication and parameter transport is that of Waldspurger,
*La formule de Plancherel pour les groupes p-adiques* (2003), Lemma V.3.2,
printed p. 295, PDF p. 61. The proof uses the actual target-fiber
identification and extends dense agreement in compact charts.
[Original publication](https://doi.org/10.1017/S1474748003000082)
