# Actual Fourier partner of the rank-one comparison box

Author: Worker 623.

This internally derived helper identifies the actual compact-open box test in
`RankOneMatrixWhittakerComparisonBox` with the affine lattice test computed in
`RankOneMatrixFunctionalEquationComparisonLatticeFourier`. It retains the
canonical topology of the supplied p-adic field, an arbitrary continuous
nontrivial unitary additive character and the supplied scalar additive Haar
measure. There is no self-duality assumption in the computation.

For actual matrix rank `n+1`, the original box has level `A` at `(0,0)`, level
`q` elsewhere in the first row and level `-a` in all remaining entries, centred
on the identity in those remaining rows. The Fourier support has level
`conductor(ψ)-A` at `(0,0)`, level `conductor(ψ)-q` elsewhere in the first row
and level `conductor(ψ)+a` in all remaining entries. The plus Fourier formula
is the product of the original scalar lattice masses, times the phase
`ψ(sum_i Y_(i+1,i+1))`, times the characteristic function of that dual
support. It holds on the full matrix space, including singular matrices.
Every genuine `MatrixFourierPair` partner is forced to have this formula.

The implementation identifies the image of the actual maximal-ideal power
with the corresponding negative-index valuation lattice. It constructs an
integer uniformizer with normalized discrete valuation `exp(-1)`, identifies
the maximal ideal with its principal ideal using valuation-integer laws,
then computes its powers. The box-set equality is entrywise. Equality of the
Schwartz tests follows from their actual indicator formulas. The published
rectangular lattice Fourier computation and the trailing-diagonal centre
pairing give the displayed result.

Provenance is internal: this is an algebraic specialization of the published
box and scalar-lattice definitions and the rectangular Fourier helper.
It asserts no convergence of Whittaker or matrix zeta integrals, no
same-vector block-zero extraction and no gamma functional equation.
