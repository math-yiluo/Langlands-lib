# From the distributional σ-lift identity to the Shintani identity

`sigmaLiftCharacterIdentityForward` proves the conditional forward direction of
`SigmaLiftCharacterIdentityStatement`. It assumes `TwistedCharacterRegularValuesStatement`
at both the ordinary degree-one and twisted universe instances, `RegularTransferStatement`,
`ConcordantIntegralEqualityStatement`, and `SigmaRegularOpenStatement`.
`RegularOpen` supplies the openness premise from the existence clause of
`CyclicNormLemmaStatement`.

At an associated regular pair \((\delta,\gamma)\), the regular-values premises
give a twisted value \(b\) and an ordinary value \(a\). The degree-one case gives
the ordinary value using the identity intertwiner. Choose Haar measures and use
the corresponding open neighborhoods from the two local values. Openness of the
σ-regular locus gives a compact open neighborhood \(K\) of \(\delta\) contained
in both the local-value neighborhood and the σ-regular set. Transfer the
indicator of \(K\) to an ordinary test function.

The coefficients of the cyclic norm and of the base-changed matrix give a
common continuous invariant at associated pairs. Over the ordinary group,
equality of these coefficients gives equality of the characteristic polynomial
over the base field. The characteristic polynomial of \(\gamma\) is
separable, hence squarefree. `matrixConj_of_squarefree_charpoly_eq`
puts its fiber in the conjugacy saturation of its local-value neighborhood.
The image of the part of the ordinary support outside that
saturation is compact and avoids the parameter of \(\gamma\). A clopen
neighborhood of the parameter disjoint from that image cuts both functions,
preserving concordance. The twisted function is still a compact open
indicator, and its support contains \(\delta\).

The two local values evaluate the distributional identity on these cutoffs,
using conjugation transport and locality for the ordinary test function.
The weight-one matched integration identity makes their integrals equal.
The twisted compact open indicator has positive finite Haar mass, so
cancellation gives \(b=c a\). The proof returns the original local-value
witnesses, which apply to all Haar measures.

Henniart–Lemaire (2011), II.2.11, printed pp. 72–73, also uses a compact
neighborhood of \(\delta\), transfer, and cancellation of a common Weyl
integral. The Lean proof localizes an existing transferred function using
characteristic-polynomial coefficients.
