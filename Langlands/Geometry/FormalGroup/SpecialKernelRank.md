# Integral height divisibility for special formal modules

Let \(q\) be the cardinality of the base residue field and \(d\) the reduced division degree. This module derives the divisibility by \(d\) of the \(q\)-normalized integral height of an actual order-linear isogeny between special coordinate formal modules over a geometric residue field.

`specialCyclicCoordinateIso` constructs actual formal coordinates from a chosen ordering of the residue embeddings. The tangent eigenline coordinates are reindexed by those embeddings. A finite-order lift of a primitive residue unit acts diagonally in the new formal coordinates. Its weights are the images of the residue unit under the ordered embeddings, and each has order \(q^d-1\).

`SpecialModule.dvd_integralHeight` uses one ordering and one integral lift for both modules. Order linearity makes the transported isogeny intertwine their diagonal endomorphisms. The represented kernel keeps its rank \(q^h\) under transport, and the diagonal kernel congruence gives \(q^h\equiv 1\pmod{q^d-1}\). Reducing the exponent modulo \(d\) gives the same congruence for the remainder \(r\). If \(0<r<d\), then \(0<q^r-1<q^d-1\), contrary to divisibility by \(q^d-1\). Thus \(d\) divides \(h\).

The special tangent condition is from Drinfeld, *Coverings of p-adic symmetric regions* (1976), §2A, printed p. 109 (PDF p. 3). The argument uses the full integral order action on the represented kernel and derives the divisibility needed for the primal height coordinate of Harris, *Supercuspidal representations in the cohomology of Drinfel'd upper half spaces* (1997), Appendix (A.3), printed p. 114 (PDF p. 40).
