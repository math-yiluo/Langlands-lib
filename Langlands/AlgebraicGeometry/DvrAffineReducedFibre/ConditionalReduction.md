# Conditional proof of the affine reduced fibre theorem

In every universe, universal Japanese finiteness for complete Noetherian
local rings and the scheme reduced fibre theorem imply
`Langlands.AlgebraicGeometry.DvrAffineReducedFibreStatement` in that universe.
The scheme premise is used with the fraction field and schemes in the same
universe as the base ring.

The proof first works over a complete DVR with algebraically closed residue
field. Universal Japanese finiteness applied to its prime quotients supplies
the Nagata hypothesis of the scheme theorem. The integral closure of the DVR
in the finite fraction-field extension supplied by that theorem is a
faithfully flat complete DVR extension with the same residue field. The
existing finiteness theorem for normalization over a complete DVR with
perfect residue field gives the finite-module conclusion.

The scheme-to-affine comparison identifies the normalized scheme with the
spectrum of the integral closure in the smooth generic fibre. The isomorphism
over the extended base identifies the closed fibres. At every generic point
of that fibre the scheme premise supplies a smooth neighbourhood in the
normalization. Restriction and base change give a reduced fibre stalk. The
local rings of the affine normalization are integrally closed domains, and
the extended base uniformizer acts regularly, so generic reducedness of the
closed fibre gives reducedness of the whole closed fibre. The residue test
over the perfect residue field gives reducedness after every field-valued
base change. The complete-base reduction then gives the assertion for the
original arbitrary DVR.

This implication uses the named scheme premise for the smooth neighbourhood
step and follows the generic-to-global reducedness argument in Conrad's
Remark A.7. The two hypotheses of the implication remain inputs.
[Conrad's appendix to Prasad–Yu, pp. 28–33](https://math.stanford.edu/~conrad/papers/qrg.pdf#page=28)
[Stacks Project, Tag 09IL](https://stacks.math.columbia.edu/tag/09IL)
