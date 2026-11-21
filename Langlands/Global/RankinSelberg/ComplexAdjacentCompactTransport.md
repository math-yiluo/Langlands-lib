# Fourier transport of finite compact orbit spans

If the left unitary translates of a square Schwartz function span a
finite-dimensional complex space, the translates of its square Fourier
transform span a finite-dimensional space as well.
`complexAdjacentCompactTransport` proves this by lifting the span to
Schwartz functions and applying the linear Fourier transform.
Unitary covariance identifies the translated transforms using inverse
transpose on the compact group.

`exists_inducedUnitaryMeasure` identifies the compact Haar integral
presented with the Borel space of the subgroup with the same integral
presented with the measurable space induced from the general linear
group. The proof uses the Borel space of the subtype topology and
transports finiteness and Haar invariance along the resulting equality.

These auxiliary identities let the compact averaging step in Section
8.3 of Hervé Jacquet, *Archimedean Rankin–Selberg Integrals*, 2009,
DOI `10.1090/conm/489/09547`, use a single finite compact expansion
on both sides.
