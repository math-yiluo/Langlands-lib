# Source quotient Haar at the literal semistandard compact trace

`LeviModel.sourceQuotientHaar` constructs Haar on the quotient of the
literal Levi point group by the split-center point image. It normalizes
the specified Borel quotient by assigning mass one to the image of
\(K \cap M(F)\). The trace is compact by closedness of the Levi and
open by restriction from \(K\). Its quotient image is compact and open.
`sourceQuotientHaar_normalized` proves the exact mass condition, so
`normalizedQuotientHaar_iff_eq_weil` identifies this measure with the
Weil measure formed from the two trace-normalized Haar measures.

For a split component the central image is closed. Reductive
unimodularity of the literal Levi gives right invariance of this Haar
on the closed central quotient, and hence invariance under inversion.
This is the measure used for square integrability and formal degree
with the compact normalization of Waldspurger I.1 and III.1.

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques
(d'après Harish-Chandra)*, 2003, I.1, printed p. 240, and III.1, printed
pp. 263–265.
[DOI 10.1017/S1474748003000082](https://doi.org/10.1017/S1474748003000082).
