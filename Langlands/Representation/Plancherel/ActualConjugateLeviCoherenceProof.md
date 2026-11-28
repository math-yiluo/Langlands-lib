# Actual conjugate-Levi coherence of Waldspurger V.3.2

`Langlands.Plancherel.ActualConjugateLeviCoherence.closedV32` proves
`ClosedV32Statement` for connected reductive groups over nonarchimedean
local fields, with independent field and representation-carrier universes.
Under `HasSourceNormalization`, it gives existence at compatible conjugate
quotient Haar scales, presentation independence, identity, composition in
the order \(st\), and both inverse equations. The equations hold at every
unitary parameter through the canonical fiber transports.

`existenceLaw` composes the actual unitary translation with a normalized
common-Levi continuation in the conjugate Levi. The preservation results for
the translation give the coefficient identity and the equality of the forms
at the specified Haar scales. `presentationIndependence` identifies
independently chosen continuations by the common-Levi coherence theorem.

The identity, composition, and inverse proofs compare coefficient-preserving
maps in fixed compact charts. Local finiteness of the continuations and
constancy of the translation and the canonical transports give the needed
weak continuity. Dense coefficient injectivity comes from the actual
dense unitary irreducibility theorem. Agreement on that dense set extends to
all unitary parameters, including reducible inductions. For the inverse law,
surjectivity supplies the second inverse equation.

The source is J.-L. Waldspurger, *La formule de Plancherel pour les groupes
p-adiques (d'après Harish-Chandra)*, J. Inst. Math. Jussieu 2 (2003), 235–333.
V.3 formula (1) and Lemmas V.3.1–V.3.2 are on printed p. 295 (PDF p. 61).
The source Haar normalization is in I.1, printed p. 240 (PDF p. 6).
The proof uses the Library's actual translations and common-Levi continuations
and extends the equations by weak continuity in the compact picture.
[Original publication](https://doi.org/10.1017/S1474748003000082)
