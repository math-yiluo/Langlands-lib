# Removal of low rotation Fourier modes in real compact pictures

`highModes` subtracts all rotation Fourier components with \(|j|<m\)
from a continuous function on the real general linear group. Each
coefficient is divided by \(2\pi\), the length of the integration interval.
The list operator `highModesList` composes these linear maps. For a list
of disjoint rotation blocks, every low mode of every listed block
vanishes after applying the list operator.

At a single block, the phase of each coefficient under a left rotation
and orthogonality of the exponential modes show that the subtraction
kills the designated coefficients. Coefficients of disjoint blocks
commute, so a later filter preserves the vanishing at another block.
The operator fixes functions whose designated coefficients already
vanish and preserves compact finiteness. It respects agreement on
\(O(n)\) because all the left rotations stay in the compact group.
A diagonal sign reflection either preserves the rotation angle or
negates it. The chosen set of modes is stable under negation, so the
filter preserves any existing eigencondition for a sign reflection.

This is an internal consequence of the Library's block rotation
coefficient, compact finiteness, and sign reflection formulas.
