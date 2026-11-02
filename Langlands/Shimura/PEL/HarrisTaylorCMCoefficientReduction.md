# Full Harris coefficient reductions on original opposite CM levels

Author: Worker 57.

This internal construction transports the already constructed full Harris
lattice reductions to the original opposite finite-adelic CM level group.
It constructs small normal coefficient levels and actions of the exact
`SmallCMResidualGroup` used by the CM scheme tower. The final coefficient
action has finite module and finite group, and is faithful.

The ordinary coefficient representation and the CM group have different
multiplications. For a topological group G, the map
`inverseOppositeContinuousEquiv` sends g to op(g inverse); its inverse sends
h to unop(h) inverse. These are multiplicative continuous inverses.
`CompactOpenLevel.inverseOpposite U` is the inverse image of U under this
homeomorphism, so openness and compactness are proved.
`inverseOppositeEquiv U` restricts inverse-unop to the actual level groups;
its displayed formula and continuity are proved.

For the original unitary data D, a small CM level U, a number field K, an
algebraic representation of `D.rationalInvolution.baseChange K` on a finite
K-module W, and an actual rational finite place p, form the ordinary level
above. `cmHarrisFiniteTorsionAction` restricts the existing action on the full
Harris lattice modulo the kth power of the rational scalar m along this
level-group isomorphism. Scalars remain the actual quotient ring
`HarrisCoefficientReductionRing K p m k`, including all coefficient places
above p. Its representative formula is the original lattice action at
inverse-unop followed by quotient projection.

`cmHarrisCongruenceKernel` is the actual kernel of that action.
Its equality with the inverse image of `harrisCongruenceKernel` proves
normality, the simultaneous one-place membership criterion, and openness
when m is nonzero. Finiteness of the underlying coefficient module is
inherited from the proved full-lattice reduction theorem.

For nonzero m, `cmHarrisCoefficientLevel` takes the ambient image of this
open kernel in U. The imported compact-open sublevel constructor proves
compactness and openness. It is sufficiently small because it is a
subgroup of the original small level U. Its subgroup inside U is proved
equal to the action kernel. Thus it is normal in U; no level-smallness or
normality witness is supplied for the new level.

For any original normal CM level V with its subgroup inside U contained in
the kernel, `cmHarrisResidualCoefficientAction` descends the actual action
to `SmallCMResidualGroup D U V`. Its quotient representative equation
retains inverse-unop. `cmHarrisCoefficientAction` specializes to the
constructed kernel level, where containment follows from the proved
equality. The quotient action is injective because its defining normal
subgroup is exactly its kernel. The existing residual-group finiteness
theorem and full coefficient finiteness theorem prove both finiteness
assertions.

The motivating originals are Harris (1999), *Galois properties of
cohomological automorphic forms on GL(n)*, Section 3, printed pp.306–308,
especially (3.7), the normal congruence levels and the factorization before
(3.8), registered as
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`;
and Harris–Taylor, *The Geometry and Cohomology of Some Simple Shimura
Varieties* (2001), III.1, printed pp.90–91, PDF pp.98–99, registered as
`harris-taylor-2001-geometry-cohomology-simple-shimura`, SHA-256
`5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.
The latter gives right frame composition, small levels and the normal U/V
Galois assertion. The inverse-unop transport and exact kernel-level
construction here are internal deductions, not separately asserted source
theorems. They fix the coefficient action used for the existing opposite
CM group; no identification with a different source normalization is
asserted. The finite full reductions are not asserted free over their
quotient ring, and their kernels are not asserted to have trivial total
intersection.

This module constructs coefficients and actual small level indices. It
does not construct a scheme, a coefficient sheaf, a descent comparison,
a canonical model or a comparison between ordinary and CM moduli.
The original inverse-right scheme action remains unchanged. Source
normalization comparisons and the remaining representability, dual
geometry and rigidity obligations remain explicit in their existing
modules.
