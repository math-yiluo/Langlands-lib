# Proof of finite signed chamber lattice charts

The internal proof combines the published `finiteChamberLattice` with a basis
of the common pairing kernel. It adds no algebraic-group or representation
hypotheses.

`SignedChamberLattice.pairingKernel` is the integral submodule annihilated
by all the pairings. The ambient module is finite and torsion-free, so its
kernel submodule is finite and torsion-free as well. The PID basis theorem
`Module.basisOfFiniteTypeTorsionFree'` supplies a finite integral basis.

`basis_signed_orthant` takes the sign and natural absolute value of each
integer basis coordinate. Thus every kernel element is a nonnegative
combination of one signed basis, among the finitely many sign functions.

`independent_join` proves independence of each joint family. Applying one
pairing to a zero relation kills every kernel term and every other root-axis
term. The remaining diagonal pairing is nonzero, so its root-axis coefficient
vanishes. Independence of the signed kernel basis kills the remaining
coefficients. The root-axis pairings are positive on the diagonal and zero
elsewhere; signed kernel pairings are all zero. Hence every generator has
nonnegative pairing with each label.

Finally the original finite-chamber theorem writes a chamber element as a
finite translate plus a nonnegative root-axis combination plus a kernel
element. Substituting its signed-basis expression gives the claimed finite
chart cover. Empty label types and zero kernel rank require no separate
case.
