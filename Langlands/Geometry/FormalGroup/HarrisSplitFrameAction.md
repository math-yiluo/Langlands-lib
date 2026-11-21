# Inverse precomposition on split affine point data

`orderAutBaseChange` pulls back the actual rational frame automorphism
as a group homomorphism. Its order equation is the pullback of the
original order equation.

On an affine test, `actFrame` pulls the primal frame automorphism back
to the special fibre, inverts it, and precomposes the primal rigidifier.
The resulting point has the original target and multiplier `t⁻¹ * c`,
where `t` is the frame similitude's multiplier and `c` is the original
rigidifier's multiplier. `inverseFrameOnSpecialFibre` constructs the
full split inverse frame map on the actual special fibre, with primal
block the inverse automorphism and scalar `t⁻¹` in the split formula.

This is the inverse-precomposition convention of Harris (1997),
Appendix, printed p. 113 (PDF p. 39), for the frame action on C1.
Rapoport–Zink (1996), Definition 3.22, printed p. 82 (PDF p. 96),
gives the left action on framed pairs. This module gives the operations
on the split affine point data.
