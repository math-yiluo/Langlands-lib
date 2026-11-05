# Actual regular-function first jets of affine point curves

This internal compatibility construction defines a first jet by its values on
all actual global regular functions. The constant coefficient of the specified
dual-number point is the curve value, and its epsilon coefficient is the real
derivative. Postcomposition pulls back regular functions. Constant curves use
the actual coefficient-extension map. Tensor induction proves that the usual
product rule agrees with multiplication in the dual-number ring.

`CoordinateJet.mul` proves closure under actual point multiplication for
every affine group scheme. The implementation first treats spectra of
commutative Hopf algebras. The spectrum point equivalence identifies group
multiplication with convolution of algebra homomorphisms, and induction on
the comultiplication tensor reduces the assertion to addition and the
ordinary product rule. An actual group-scheme isomorphism from a Hopf
spectrum transports this proof to the original affine group scheme.

The base ring and the coefficient algebra share an arbitrary universe.
The coefficient algebra is a normed commutative real algebra with its
specified base-ring algebra structure. No topology or continuity of the
base-ring map, completeness, finite generation or nontriviality is required.
The multiplication lemma requires affineness; postcomposition and constant
curves do not.

This is internal first-order compatibility infrastructure for comparing
the analytic and algebraic differentials of genuine representations. It
does not itself assert that comparison.
