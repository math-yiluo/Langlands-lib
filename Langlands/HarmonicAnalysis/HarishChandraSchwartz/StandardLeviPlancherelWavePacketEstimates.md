# Internal fixed-level reduction for the source-normalized packet

This internal conditional construction uses the exact original packet data and
source normalization. It does not establish the derivative estimates or prove
VI.3.1 under the original target's premises alone.

The same-input-subgroup invariance theorem specializes the generic fixed-level
coefficient and packet argument to the literal standard Levi and the actual
Plancherel weight and source-normalized measure. It applies to every section
at a fixed input level without shrinking the subgroup.

`StandardLeviPacketDerivativeEstimates` is the remaining analytic obligation:
each real output exponent on each fixed level has a finite set of input
derivative seminorms and a nonnegative constant, uniform in the section,
bounding the actual extended Schwartz seminorm for `rationalXi` and the full
matrix `rationalHeight`. It uses the existing function-valued algebraic packet
map, composed with the identity from the section space to smooth sections.

`standardLeviPacketSchwartzFromEstimates` applies the generic synthesis
construction to these estimates, using same-subgroup invariance to discharge
its algebraic hypothesis. The resulting continuous linear map has the literal
original integral as its pointwise values. The internal reduction
`standardLeviPlancherelWavePacketSourceNormalized_of_estimates` combines this
map with the proved compact-orbit integrability to obtain the original joint
target, conditional on the displayed derivative estimates.

This is a derived implementation of the topological endpoint suggested by
Waldspurger VI.3.1, printed pp.302-305/PDF pp.68-71. It changes no published
target or imported pair. The derivative estimates remain to be proved from the
original assumptions, by the actual central Fourier, lower-Levi weak term,
positive term, Xi and full-height arguments or an independent analytic proof.
The conditional reduction is not a proof of the task's exact target.
