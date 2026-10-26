# Positive PEL algebraic input retaining the original Harris group

This internal construction takes a proof of the specific proposition
`PositiveRationalSkewTwistExists D C` as an explicit input. That proposition
has a separate proof task. This module does not prove it or assume it as
an axiom. All constructions below retain that proof argument.

Write sigma for the original Harris involution. A witness beta has
sigma(beta) = -beta and makes

    tau(x) = beta sigma(x) beta inverse

positive on the actual real algebra. The original sigma carries the Harris
group signatures; tau is the auxiliary positive left involution needed
by the algebraic PEL construction.

## The actual algebra and form

`skewTwist D beta hbeta` constructs a new `CentralSimpleUnitaryData` on
the same number fields and algebra A, with involution tau. Conjugation
by a unit fixes central elements, so the center action remains the
specified CM conjugation. Centrality, simplicity, dimension, finiteness
and n > 1 are inherited from D. No Harris-signature assertion is made
for tau.

`positivePELUnit` chooses beta from the existence proof.
`positivePELAlgebra` applies `skewTwist` to it and
`positivePELAlgebra_isPositive` obtains exactly the required real
positivity from that proof.

The inverse gamma = beta inverse is skew for tau. The generic theorem
`AlgebraInvolution.skewAdjoint_inverse` proves

    gamma tau(x) gamma inverse = sigma(x).

The proof uses the displayed inner-conjugation formulas and cancels the
two units. This is equality of algebra involutions, including their
actual scalar-linear maps.

`positivePELForm` constructs the normalized rational trace pairing using
the positive left involution tau and gamma. The previous trace-form
theorems give alternation and nondegeneracy. The theorem
`positivePEL_rightAdjoint` identifies its right-adjoint involution with
the original rational Harris involution sigma.

`positivePELSimilitudesEquiv` therefore gives an actual group equivalence
from the opposite of the original rational Harris similitude group to
the A-linear similitude group of this form, by the preceding
trace-similitude comparison. The opposite convention is the one for
right multiplication. The right-adjoint identity, right-multiplication
action formula and equality of the recorded multipliers are also proved.

## Provenance and remaining obligations

The construction is an intrinsic combination of the existing skew-adjoint
involution, normalized trace form, group comparison and exact positive
rational-twist proposition. Its algebra and form are constructed from the
actual unit witness. It accepts no arbitrary output form, group or model.

Until the separate existence theorem is proved and published, this remains
a construction conditional on its explicit proof argument. Positivity
here concerns the auxiliary algebra involution. It does not assert
positivity of a polarization form relative to a Hodge homomorphism,
choose a polarization sign, prove any finite-place condition, construct
lattices or adelic scalar extensions, or supply a moduli scheme.
