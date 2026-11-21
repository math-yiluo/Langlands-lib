# Shrinking orbit averages in the smooth test topology

A positive dilation sends a compact orbit test to a smooth test whose
support lies in the dilated support of the original test. The reciprocal
volume factor gives the stated change of variables against an additive
Haar measure. The dilated compact support eventually lies in every open
neighborhood of the origin.

For a fixed scalar orbit test and a globally smooth operator-valued
kernel, evaluate the kernel at the slice coordinate and the dilated
orbit coordinate. Apply it to a fixed slice test and integrate against
the orbit test. The resulting family of slice tests is continuous in
the smooth test topology. Indeed, all members are supported in the
original slice support, and smooth dependence of the integrand on the
compact orbit support passes through the continuous linear integration
operator. The integration uses Mathlib's Bochner integral convention.
With a complete output space and an orbit test of integral one, at zero
dilation the family is the kernel at orbit coordinate zero applied to
the original slice test.

This internal construction is used for the local limiting step in the
covariance of leading transverse distribution coefficients.
