# Exact local simple-root coefficient nonvanishing

`splitSimpleRootHighestCoefficientNonvanishing` proves the published proposition `SplitSimpleRootHighestCoefficientNonvanishingStatement.{u}` from `SimpleRootHighestCoefficient`, with exactly that proposition as its type. It preserves every supplied affine group scheme, split pinning, finite matrix representation, highest weight, simple root of integral coroot pairing one, normalized root map, reflection representative and nonzero highest vector in the target.

The proof introduces the target's arguments and applies the published arbitrary-field theorem `SplitPinning.NormalizedRootParametrization.coefficientMatrix_one_reflected_ne_zero` from `SimpleRootHighestCoefficientNonvanishing`. That theorem requires only a field, so it applies to the algebraically closed field supplied by this target. The full highest-weight hypothesis and the same supplied root and representative are passed unchanged. There is no new argument about rational-point density, scalar normalization or positive characteristic.

This is an internal specialization of the published arbitrary-field proof. Its supporting module documents the integral-cone, whole-root-action and character-projector argument; this module imports that proof without changing either paired dependency. Worker 1284 isolated the local target, and Worker 1317 implemented the stronger proof and this specialization.

This local proof supplies a nonzero coefficient, with no prescribed scalar value. It constructs no highest-weight representation, proves no ascent of simple connectedness and does not prove the final split Steinberg quotient statement.
